// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// End-to-end suite for the two bid-integrity dispute classes and their resolvers/timeout.
// Surface under test: ISessionAuction plus the integrity fields on Lot/IntegrityDispute in
// HammerTypes.sol. The behaviors exercised:
//   - challengeOverCeiling (Class A) is self-proving: records harm atomically, never increments
//     lot.bidIntegrityOpen, never gates release. The offending seq may be a losing bid.
//   - challengeOverCeiling gates: NotPrincipal, CommitmentMismatch, NotOverCeiling (the check is
//     strictly bidAmount > maxBid; an at-ceiling bid is on-policy).
//   - challengeAttestation (Class B) posts a refundable bond, opens a gated dispute
//     (bidIntegrityOpen++), and allows one open Class B dispute per seq (double-open reverts
//     AlreadyDisputed).
//   - resolveBidIntegrityDispute (onlyArbiter): uphold refunds the bond and records harm, reject
//     pays the bond to the seller; either way clears open and decrements bidIntegrityOpen.
//   - timeoutBidIntegrityDispute (permissionless): WindowOpen before the timeout, resolves
//     against the silent challenger after it (bond to seller, byTimeout=true); a Class A or
//     not-open seq reverts WrongDeliveryState.
//   - the release gate is asymmetric: an open Class B freezes only the seller-paying release;
//     Class A never freezes release.
//
// Negative tests assert a specific error selector (never a bare expectRevert); positive tests
// build the pre-state through the real entrypoints and assert exact events and state.

import {HammerBase} from "./HammerBase.t.sol";

import {SessionAuction}  from "../src/SessionAuction.sol";
import {Clones}          from "@openzeppelin/contracts/proxy/Clones.sol";
import {ISessionAuction} from "../src/interfaces/ISessionAuction.sol";
// Bond interface (concrete AgentBond is wired in HammerBase as `operatorBond`).
// recordClaim(sessionId, victim, provenHarm) is the onlyAuction harm-ledger write every upheld
// claim makes (Class A self-proving, and Class B on uphold).
import {IOperatorBond} from "../src/interfaces/IAgentBond.sol";
// AgentBond.recordClaim emits ClaimRecorded; imported so the no-mock uphold test can assert it fires.
import {AgentBond} from "../src/AgentBond.sol";
import {MockERC20}     from "./mocks/MockERC20.sol";
// KYC registry read by placeBid (paddleOf == 0 -> Unauthorized). The stub returns 0, so every
// accepted bid must vm.mockCall paddleOf to a nonzero paddle; imported only to build that mock.
import {IPaddleRegistry} from "../src/interfaces/IPaddleRegistry.sol";
import {
    Ceiling,
    AttestationQuote,
    Lot,
    LotPhase,
    DeliveryState,
    CEILING_TYPEHASH
} from "../src/types/HammerTypes.sol";

// Guard SessionAuction inherits; supplies the ReentrancyGuardReentrantCall() selector. All four
// integrity entrypoints are nonReentrant.
import {ReentrancyGuardTransient} from "@openzeppelin/contracts/utils/ReentrancyGuardTransient.sol";

// Hostile recipients (file-level, F_-prefixed to avoid cross-test symbol collisions). The bonded
// paths _pay these (bond refund to challenger on uphold, bond to seller on reject/timeout). A
// failing payout must credit _pendingWithdrawals (WithdrawalCredited) rather than revert the
// resolution; the reentrant variant proves the nonReentrant guard fires on re-entry.

/// @dev Native receiver whose receive() reverts while `reject` is true, driving the gas-capped
///      `_pay` push-failure -> `_pendingWithdrawals` credit fallback. Toggle to accept so
///      claimPending then pulls the parked bond.
contract F_RejectingReceiver {
    bool public reject = true;

    function setReject(bool v) external {
        reject = v;
    }

    receive() external payable {
        if (reject) revert("F: no ether");
    }
}

/// @dev ERC-20 whose `transfer` returns false (never reverts) while `fail` is true, driving the
///      `SafeERC20.trySafeTransfer` -> false -> `_pendingWithdrawals` fallback on the ERC-20 bond
///      payout. `transferFrom` always succeeds, so only the push leg fails.
contract F_FalseReturningERC20 is MockERC20 {
    bool public fail = true;

    constructor() MockERC20("F False USD", "ffUSD", 6) {}

    function setFail(bool v) external {
        fail = v;
    }

    function transfer(address to, uint256 value) public override returns (bool) {
        if (fail) return false; // trySafeTransfer observes false without reverting
        return super.transfer(to, value);
    }
}

/// @dev Hostile recipient that re-enters a target nonReentrant integrity entrypoint when paid via
///      `_pay`, capturing the nested-call revert selector (so a test can assert the guard fired even
///      though the gas-capped `_pay` swallows the failure into _pendingWithdrawals). mode: 0
///      re-enters resolveBidIntegrityDispute (same function), 1 re-enters
///      timeoutBidIntegrityDispute, 2 is a cross-function re-entry into challengeAttestation (so the
///      shared transient guard is exercised across entrypoints, not just same-function).
contract F_ReentrantReceiver {
    ISessionAuction private immutable auctionRef;
    uint256 private immutable lotId;
    uint64  private immutable seq;
    uint8   private immutable mode;

    // One slot records the whole outcome so the capture fits inside the gas-capped (50_000) `_pay`
    // push. `_result` is 0 until re-entry is attempted; afterwards bit 32 (TRIED) is set and the low
    // 32 bits hold the nested-call selector. A low-level call (no try/catch returndata copy) keeps
    // receive() to one CALL + one cold SSTORE, well under the budget, so out-of-gas before the
    // SSTORE is not reachable. This distinguishes three outcomes: a blocked re-entry sets
    // reentered() with caughtSelector() == ReentrancyGuardReentrantCall; a guard-absent re-entry
    // sets reentered() with caughtSelector() == 0 (the nested call succeeded); out-of-gas leaves
    // reentered() == false.
    uint256 private _result;
    uint256 private constant TRIED = 1 << 32; // bit 32 marks "re-entry attempted" (above the selector)

    constructor(ISessionAuction auction_, uint256 lotId_, uint64 seq_, uint8 mode_) {
        auctionRef = auction_;
        lotId = lotId_;
        seq = seq_;
        mode = mode_;
    }

    /// @notice True once the receiver attempted the nested re-entry.
    function reentered() external view returns (bool) {
        return _result != 0;
    }

    /// @notice The selector the nested re-entrant call reverted with (0 if it did not revert, meaning
    ///         the guard failed to block re-entry).
    function caughtSelector() external view returns (bytes4) {
        return bytes4(uint32(_result)); // low 32 bits hold the captured selector
    }

    receive() external payable {
        if (_result != 0) return; // re-enter exactly once (avoid unbounded recursion)
        bytes memory cd;
        if (mode == 0) {
            cd = abi.encodeCall(ISessionAuction.resolveBidIntegrityDispute, (lotId, seq, false, uint128(0)));
        } else if (mode == 1) {
            cd = abi.encodeCall(ISessionAuction.timeoutBidIntegrityDispute, (lotId, seq));
        } else {
            // Cross-function: re-enter a different nonReentrant entrypoint. nonReentrant runs before
            // the function body (before the native-rail WrongBond check), so a value-0 cross-call
            // trips the shared transient guard first. seq is the other (loser) seq, so absent the
            // guard it would be a distinct, not-yet-open dispute.
            cd = abi.encodeCall(ISessionAuction.challengeAttestation, (lotId, seq, hex"deadbeef"));
        }
        (bool ok, bytes memory ret) = address(auctionRef).call(cd);
        bytes4 sel = (!ok && ret.length >= 4) ? bytes4(ret) : bytes4(0);
        _result = TRIED | uint256(uint32(sel)); // single cold SSTORE: marker | selector
    }
}

contract BidIntegrityTest is HammerBase {
    // The lot every test drives; opened by the hammer factory in _bootstrapHammeredLot.
    uint256 private constant LOT_ID = 1;

    // Guards the one-shot session initialize so a second bootstrap (tests that use more than one
    // lot) opens a fresh lot on the same session instead of re-initializing (which would revert
    // InvalidInitialization).
    bool private _sessionInited;

    // (maxBid, salt) opening pairs for the ceiling commitment. salt is the client-side secret;
    // commitment == keccak256(abi.encode(maxBid, salt)), the preimage challengeOverCeiling reopens.
    //
    // Winning bid (seq 2, bidder2): lands on-policy strictly below its committed ceiling.
    uint128 private constant WINNER_MAXBID = 5 ether;     // committed ceiling for the winning bid
    uint128 private constant WINNER_AMOUNT = 3 ether;     // landed amount < WINNER_MAXBID: on-policy
    bytes32 private constant WINNER_SALT   = keccak256("F_DOMAIN_WINNER_SALT_v1");

    // Offending bid (seq 1, bidder1): a LOSING bid landed over its committed ceiling, so a Class A
    // proof succeeds on a non-winning seq. provenHarm == OVER_AMOUNT - OVER_MAXBID (the stored bid
    // amount minus the committed ceiling). OVER_AMOUNT < WINNER_AMOUNT keeps seq 1 a loser;
    // OVER_AMOUNT > OVER_MAXBID makes it over-ceiling.
    uint128 private constant OVER_MAXBID   = 1 ether;     // committed ceiling for the offending seq
    uint128 private constant OVER_AMOUNT   = 2 ether;     // landed amount > OVER_MAXBID, < WINNER_AMOUNT
    bytes32 private constant OVER_SALT     = keccak256("F_DOMAIN_OVER_SALT_v1");

    // Bid-path signing keys. placeBid recovers the ceiling signature to c.principal, so each bidding
    // principal needs a private key whose address equals its HammerBase actor. makeAddrAndKey is
    // address-stable with makeAddr, so re-deriving the named bidders yields the same addresses
    // HammerBase.setUp() produced, now with their signing keys.
    uint256 private bidder1Key;
    uint256 private bidder2Key;
    uint256 private bidder3Key;

    function setUp() public override {
        super.setUp();
        (, bidder1Key) = makeAddrAndKey("bidder1");
        (, bidder2Key) = makeAddrAndKey("bidder2");
        (, bidder3Key) = makeAddrAndKey("bidder3");
    }

    // Bid-path plumbing helpers. Feed the placeBid pre-state (ceiling ECDSA sig + KYC paddle) so the
    // bid clears the signature check (BadSignature) and the KYC check (Unauthorized) and reaches the
    // bid-integrity surface under test.

    // EIP-712 domain constants for a clone (constructed EIP712("Hammer","1"); the domain
    // self-corrects to the clone address).
    bytes32 private constant EIP712_TYPE_HASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 private constant HASHED_NAME    = keccak256(bytes("Hammer"));
    bytes32 private constant HASHED_VERSION = keccak256(bytes("1"));

    /// @notice Map a bidding principal to its signing key. Reverts for an unmapped principal so a new
    ///         actor fails loudly here rather than as a confusing BadSignature deep in placeBid.
    function _signerKeyFor(address principal) private view returns (uint256) {
        if (principal == bidder1) return bidder1Key;
        if (principal == bidder2) return bidder2Key;
        if (principal == bidder3) return bidder3Key;
        revert("F: no signing key for principal");
    }

    function _domainSeparator(address clone) private view returns (bytes32) {
        return keccak256(abi.encode(EIP712_TYPE_HASH, HASHED_NAME, HASHED_VERSION, block.chainid, clone));
    }

    /// @notice Sign the Ceiling over the clone domain (matches placeBid's _hashTypedDataV4 over the
    ///         8-field CEILING_TYPEHASH struct).
    function _signCeiling(address clone, Ceiling memory c, uint256 key) private view returns (bytes memory) {
        bytes32 structHash = keccak256(
            abi.encode(
                CEILING_TYPEHASH, c.principal, c.sessionId, c.lotId,
                c.ceilingCommit, c.strategy, c.deadline, c.maxBids, c.nonceKey
            )
        );
        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", _domainSeparator(clone), structHash));
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(key, digest);
        return abi.encodePacked(r, s, v);
    }

    /// @notice Mock PaddleRegistry.paddleOf(principal) -> a nonzero KYC paddle. The stub returns 0 and
    ///         placeBid reverts Unauthorized when paddleOf == 0, so every accepted bid needs this.
    ///         Distinct per principal so lot.paddleId reflects the real bidder; only != 0 matters here.
    function _mockPaddle(address principal, uint16 paddleId) private {
        vm.mockCall(
            address(paddles),
            abi.encodeWithSelector(IPaddleRegistry.paddleOf.selector, principal),
            abi.encode(paddleId)
        );
    }

    /// @notice A stable distinct nonzero paddle for `principal`: fold the address into the low 15 bits
    ///         then set bit 15, so the result is always in [0x8000, 0xFFFF].
    function _paddleFor(address principal) private pure returns (uint16) {
        return uint16(uint256(uint160(principal)) & 0x7FFF) | 0x8000;
    }

    /// @notice Reveal the winning seq's committed (maxBid, salt) so finalizeWinner's reveal gate is met.
    ///         finalizeWinner requires the anti-collusion window closed AND (lot.revealed OR the
    ///         reveal deadline lapsed). In HammerBase the reveal deadline equals the AC window and the
    ///         deadline check is strict (>), so a warp of exactly AC_CHALLENGE_SEC leaves an unrevealed
    ///         winner reverting AcWindowOpen; revealing here satisfies the gate for any later finalize
    ///         warp >= the AC window. Reveal must be pranked as lot.highBidder (the winner principal).
    function _revealWinner(SessionAuction a, uint256 lotId, uint128 winnerMaxBid, bytes32 winnerSalt) private {
        Lot memory lot = a.getLot(lotId);
        // Read winnerSeq + highBidder into locals BEFORE vm.prank: an inline a.getLot(...) argument
        // would consume the prank, so reveal would run unpranked and revert NotPrincipal.
        uint64 wseq = lot.winnerSeq;
        address winner = lot.highBidder;
        vm.prank(winner);
        a.reveal(lotId, wseq, winnerMaxBid, winnerSalt);
    }

    // Pre-state helpers: call the real entrypoints (depositCeiling, placeBid, hammer, ...) to build
    // the end-to-end pre-state each test exercises.

    /// @notice Initialize the session clone for `paymentToken` with the default config, once.
    ///         cfg.hammer == address(hammer) (the factory), so onlyHammer paths prank it. The
    ///         once-guard makes a repeated bootstrap open a fresh lot rather than re-initialize
    ///         (a second initialize would revert InvalidInitialization).
    function _init(address paymentToken) private {
        if (_sessionInited) return;
        _sessionInited = true;
        vm.prank(address(hammer));
        auction.initialize(_defaultInitConfig(paymentToken));
    }

    /// @notice Build the commitment exactly as the client/contract does (abi.encode, NOT packed).
    function _commit(uint128 maxBid, bytes32 salt) private pure returns (bytes32) {
        return keccak256(abi.encode(maxBid, salt));
    }

    /// @notice The keyed nonceKey the bid envelope must carry (per-(session, lot, principal)).
    function _nonceKey(uint256 lotId, address principal) private pure returns (uint192) {
        return uint192(uint256(keccak256(abi.encode(SESSION_ID, lotId, principal))));
    }

    /// @notice A well-formed envelope for `principal` on `lotId` committing (maxBid, salt).
    function _ceiling(uint256 lotId, address principal, uint128 maxBid, bytes32 salt)
        private
        view
        returns (Ceiling memory c)
    {
        c = Ceiling({
            principal: principal,
            sessionId: SESSION_ID,
            lotId: lotId,
            ceilingCommit: _commit(maxBid, salt),
            strategy: 0, // incremental
            deadline: uint64(block.timestamp + 7 days),
            maxBids: 16,
            nonceKey: _nonceKey(lotId, principal)
        });
    }

    /// @notice A measurement-correct attestation quote bound to `observedPrevTop`.
    function _quote(Ceiling memory c, uint256 lotId, uint128 amount, uint64 bidIndex, uint128 observedPrevTop, bytes32 nonce) private view returns (AttestationQuote memory q) {
        return _realQuote(c, lotId, amount, bidIndex, observedPrevTop, nonce);
    }

    /// @notice Fund a bidder's free deposit on the active rail and place one bid.
    function _depositAndBid(
        uint256 lotId,
        address principal,
        uint128 prevTop,
        uint64 bidIndex,
        uint128 amount,
        uint128 maxBid,
        bytes32 salt,
        bytes32 quoteNonce
    ) private {
        // deposit > ceiling so the deposit slack hides the committed ceiling; native rail here.
        vm.prank(principal);
        auction.depositCeiling{value: 10 ether}(lotId, 10 ether);

        Ceiling memory c = _ceiling(lotId, principal, maxBid, salt);
        AttestationQuote memory q = _quote(c, lotId, amount, bidIndex, prevTop, quoteNonce);
        bytes32 keyId = _baseOperatorKeyId();
        // Real ceiling sig recovering to the principal + a nonzero KYC paddle.
        bytes memory sig = _signCeiling(address(auction), c, _signerKeyFor(principal));
        _mockPaddle(principal, _paddleFor(principal));

        vm.prank(principal);
        auction.placeBid(c, lotId, principal, bidIndex, amount, sig, keyId, q);
    }

    /// @notice Open `lotId`, land a losing bid (seq 1) then the winning bid (seq 2), and hammer.
    ///         Leaves the lot Hammered with winnerSeq naming bidder2's bid, escrow snapshotted.
    ///         Per-lot quote nonces are salted by lotId so two lots in one session never collide.
    function _bootstrapHammeredLotId(uint256 lotId) private {
        _init(address(0));

        vm.prank(address(hammer));
        auction.openLot(lotId, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));

        // seq 1: bidder1's losing bid, landed OVER its own ceiling (no prior top, prevTop == 0).
        _depositAndBid(lotId, bidder1, 0, 0, OVER_AMOUNT, OVER_MAXBID, OVER_SALT, keccak256(abi.encode("Q1", lotId)));
        // seq 2: bidder2's winning bid; prevTop is bidder1's standing top (OVER_AMOUNT).
        _depositAndBid(lotId, bidder2, OVER_AMOUNT, 0, WINNER_AMOUNT, WINNER_MAXBID, WINNER_SALT, keccak256(abi.encode("Q2", lotId)));

        vm.warp(block.timestamp + 1 days + 1); // past endsAt
        auction.hammer(lotId);
        // Reveal so each test's subsequent finalizeWinner clears the reveal gate; see _revealWinner.
        _revealWinner(auction, lotId, WINNER_MAXBID, WINNER_SALT);
    }

    /// @notice Bootstrap the default LOT_ID.
    function _bootstrapHammeredLot() private {
        _bootstrapHammeredLotId(LOT_ID);
    }

    /// @notice Open a Class B integrity dispute on `seq` by `challenger` (native rail bond).
    function _openClassB(uint256 lotId, uint64 seq, address challenger) private {
        vm.prank(challenger);
        auction.challengeAttestation{value: INTEGRITY_BOND_AMT}(lotId, seq, hex"deadbeef");
    }

    /// @notice Mock the bond's onlyAuction `recordClaim` to return a totalClaims value, so a test that
    ///         only cares about the auction-side branch is not gated by the bond's onlyAuction check
    ///         (HammerBase wires the base `auction` without registering it as a clone). vm.expectCall
    ///         still asserts the exact (sessionId, victim, provenHarm) args (mockCall does not suppress
    ///         expectCall accounting). Cleared automatically per test.
    function _mockRecordClaim() private {
        vm.mockCall(
            address(operatorBond),
            abi.encodeWithSelector(IOperatorBond.recordClaim.selector),
            abi.encode(uint256(1)) // totalClaims (value immaterial to the SUT branch under test)
        );
    }

    // Parameterized-rail helpers. The base `auction` is the native rail. These build a separate clone
    // for an arbitrary rail/seller so the bonded Class B paths are also exercised on the 6-decimal
    // ERC-20 rail (the bond moves through the rail-specific _pull/_pay), and so a hostile
    // seller/challenger can be installed.

    uint96  private constant RAIL_RESERVE = 1e6;   // token reserve (6 dp), mirrors RESERVE_PRICE
    uint128 private constant RAIL_OVER_MAXBID = 1e6;
    uint128 private constant RAIL_OVER_AMOUNT = 2e6;
    uint128 private constant RAIL_WIN_MAXBID  = 5e6;
    uint128 private constant RAIL_WIN_AMOUNT  = 3e6;

    /// @notice Deposit + place one bid for `principal` on clone `a` over `paymentToken`.
    function _depositAndBidOn(
        SessionAuction a,
        address paymentToken,
        uint256 lotId,
        address principal,
        uint128 prevTop,
        uint128 amount,
        uint128 maxBid,
        bytes32 salt,
        bytes32 quoteNonce
    ) private {
        if (paymentToken == address(0)) {
            uint256 deposit = 10 ether;
            vm.prank(principal);
            a.depositCeiling{value: deposit}(lotId, deposit);
        } else {
            uint256 deposit = 10e6;
            vm.prank(principal);
            MockERC20(paymentToken).approve(address(a), deposit);
            vm.prank(principal);
            a.depositCeiling(lotId, deposit);
        }

        Ceiling memory c = _ceiling(lotId, principal, maxBid, salt);
        AttestationQuote memory q = _quote(c, lotId, amount, 0, prevTop, quoteNonce);
        bytes32 keyId = _baseOperatorKeyId();
        // Sign over THIS clone's domain (address(a), not the base auction) + KYC paddle.
        bytes memory sig = _signCeiling(address(a), c, _signerKeyFor(principal));
        _mockPaddle(principal, _paddleFor(principal));

        vm.prank(principal);
        a.placeBid(c, lotId, principal, 0, amount, sig, keyId, q);
    }

    /// @notice Build a fresh clone on `paymentToken` with `sellerAddr`, driven to a delivered winner
    ///         (the seller-paying release point), ready for Class B disputes. Loser is seq 1, winner
    ///         seq 2. Token-rail bidders are pre-funded by HammerBase (_fundAll).
    function _freshDeliveredLot(address paymentToken, address sellerAddr)
        private
        returns (SessionAuction a)
    {
        a = SessionAuction(Clones.clone(address(impl)));
        _buildDeliveredLot(a, paymentToken, sellerAddr);
    }

    /// @notice As above but on a pre-deployed clone `a`, so a hostile seller contract that needs the
    ///         clone address at construction can be wired before openLot stores it.
    function _buildDeliveredLot(SessionAuction a, address paymentToken, address sellerAddr) private {
        vm.prank(address(hammer));
        a.initialize(_defaultInitConfig(paymentToken));

        bool native = paymentToken == address(0);
        uint96 reserve = native ? uint96(RESERVE_PRICE) : RAIL_RESERVE;
        vm.prank(address(hammer));
        a.openLot(LOT_ID, sellerAddr, reserve, uint64(block.timestamp + 1 days));

        // Per-field (no tuple-valued ternary). Loser (seq 1) lands over its own ceiling; winner
        // (seq 2) lands strictly below its ceiling (on-policy), same shape per rail.
        uint128 overAmt = native ? OVER_AMOUNT : RAIL_OVER_AMOUNT;
        uint128 overMax = native ? OVER_MAXBID : RAIL_OVER_MAXBID;
        uint128 winAmt  = native ? WINNER_AMOUNT : RAIL_WIN_AMOUNT;
        uint128 winMax  = native ? WINNER_MAXBID : RAIL_WIN_MAXBID;

        _depositAndBidOn(a, paymentToken, LOT_ID, bidder1, 0, overAmt, overMax, OVER_SALT, keccak256("RAIL_Q1"));
        _depositAndBidOn(a, paymentToken, LOT_ID, bidder2, overAmt, winAmt, winMax, WINNER_SALT, keccak256("RAIL_Q2"));

        vm.warp(block.timestamp + 1 days + 1);
        a.hammer(LOT_ID);
        // Reveal so finalizeWinner clears the reveal gate after the AC-window warp; see _revealWinner.
        _revealWinner(a, LOT_ID, winMax, WINNER_SALT);

        vm.warp(block.timestamp + AC_CHALLENGE_SEC);
        a.finalizeWinner(LOT_ID);
        vm.prank(sellerAddr);
        a.markDelivered(LOT_ID, keccak256("rail-delivery"), "ipfs://rail");
    }

    /// @notice Open a Class B dispute on clone `a` over `paymentToken` by `challenger`. The bond is
    ///         INTEGRITY_BOND_AMT base units on both rails (the config field does not scale by decimals),
    ///         so the token-rail challenger is funded + approved here. Native pulls via msg.value; ERC-20
    ///         pulls via safeTransferFrom with msg.value == 0.
    function _openClassBOn(SessionAuction a, address paymentToken, uint256 lotId, uint64 seq, address challenger)
        private
    {
        if (paymentToken == address(0)) {
            vm.prank(challenger);
            a.challengeAttestation{value: INTEGRITY_BOND_AMT}(lotId, seq, hex"deadbeef");
        } else {
            fundToken(challenger, INTEGRITY_BOND_AMT);
            vm.prank(challenger);
            MockERC20(paymentToken).approve(address(a), INTEGRITY_BOND_AMT);
            vm.prank(challenger);
            a.challengeAttestation(lotId, seq, hex"deadbeef");
        }
    }

    // Class A challengeOverCeiling is self-proving: records harm atomically, emits Opened
    // (class 0, bond 0) then ClaimUpheld in one call, writes no IntegrityDispute, and does
    // not increment lot.bidIntegrityOpen (so it never gates release). The seq may be a losing bid.
    function test_ChallengeOverCeilingSelfProving() public {
        _bootstrapHammeredLot();

        // The offending seq is the losing bid (seq 1): an over-ceiling bid need not be the winner.
        uint64 offendingSeq = 1;
        uint128 expectedHarm = OVER_AMOUNT - OVER_MAXBID; // bidAmount - maxBid

        // The self-proving claim writes harm into the per-session OperatorBond ledger via
        // recordClaim(sessionId, victim, provenHarm); settleSlash later pays victims pro-rata by
        // recorded harm. Assert the exact call (victim == seq principal bidder1, harm == amount - maxBid).
        _mockRecordClaim();
        vm.expectCall(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder1, expectedHarm))
        );

        // Class A is a pure external-ledger write into the bond (the slash pool, not an escrow
        // freeze, is the remedy), so it moves zero clone money: no bond pull (Class A carries no
        // bond), no escrow debit, no deposit mutation. Snapshot the clone balance, winner escrow,
        // and the disputed principal's free deposit so any of those movements is caught.
        uint256 clonePre = address(auction).balance;
        uint128 escrowPre = auction.getLot(LOT_ID).escrowAmount;
        uint256 principalFreePre = auction.withdrawableFree(LOT_ID, bidder1);

        // Both events fire in the one self-proving call: Opened(class 0/A, bond 0) then Upheld.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityDisputeOpened(LOT_ID, offendingSeq, bidder1, 0, 0); // class 0/A, bond 0
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityClaimUpheld(LOT_ID, offendingSeq, bidder1, expectedHarm);

        vm.prank(bidder1); // the recorded principal of the offending seq
        auction.challengeOverCeiling(LOT_ID, offendingSeq, OVER_MAXBID, OVER_SALT);

        // The gate is untouched, so release is not frozen.
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "Class A must not set the gate");
        assertFalse(auction.bidIntegrityDisputeOpen(LOT_ID), "Class A never opens the release gate");

        // No clone money moved on the self-proving call (no bond pull, no escrow touch, no deposit
        // mutation). The harm lives only in the external bond ledger asserted above.
        assertEq(address(auction).balance, clonePre, "Class A self-proving must move no clone funds");
        assertEq(auction.getLot(LOT_ID).escrowAmount, escrowPre, "Class A must not touch the winner escrow");
        assertEq(
            auction.withdrawableFree(LOT_ID, bidder1),
            principalFreePre,
            "Class A must not mutate the disputed principal's deposit"
        );
    }

    // The full operator-bond remedy end-to-end through the real auction and real bond (no recordClaim
    // mock). A self-proving challengeOverCeiling records harm into the live OperatorBond; the
    // permissionless, deadline-gated closeSession seals the ledger; settleSlash then claimSlash pays
    // the victim their proven harm pro-rata, remainder to Treasury. The close is driven through the
    // auction's own bondClaimsCloseAt() and sessionId().
    function test_E2E_OverCeilingToBondSettleAndClaim() public {
        _bootstrapHammeredLot();
        uint64 offendingSeq = 1; // bidder1's losing-but-over-ceiling seq
        uint128 harm = OVER_AMOUNT - OVER_MAXBID;

        // An operator stakes 2x the harm on this session so a Treasury remainder exists after the victim.
        uint256 stake = uint256(harm) * 2;
        vm.deal(operator1, stake);
        vm.prank(operator1);
        operatorBond.deposit{value: stake}(SESSION_ID, address(auction), stake);

        // Self-proving challenge (no mock): the auction records harm into the live bond.
        vm.prank(bidder1);
        auction.challengeOverCeiling(LOT_ID, offendingSeq, OVER_MAXBID, OVER_SALT);
        assertEq(operatorBond.bondOf(SESSION_ID), stake, "E2E: stake pooled, not yet slashed");

        // Permissionless close, only strictly after the bond-claim deadline.
        vm.warp(auction.bondClaimsCloseAt() + 1);
        operatorBond.closeSession(SESSION_ID, address(auction));

        uint256 treasuryBefore = address(treasury).balance;
        operatorBond.settleSlash(SESSION_ID);
        assertEq(address(treasury).balance - treasuryBefore, stake - harm, "E2E: remainder to Treasury");

        uint256 victimBefore = bidder1.balance;
        vm.prank(bidder1);
        operatorBond.claimSlash(SESSION_ID);
        assertEq(bidder1.balance - victimBefore, harm, "E2E: victim paid full proven harm pro-rata");
        assertEq(operatorBond.bondOf(SESSION_ID), 0, "E2E: bond pool fully distributed (conserved)");
    }

    // Operator non-liveness. The arbiter slashes the operator pool for a lot that received zero bids
    // despite a funded ceiling deposit (funded bid-intent), after the auction window + grace. Guards
    // bound the arbiter: a lot with any bid, or with no funded deposit, can never be slashed; the
    // slash is arbiter-only and time-gated.

    /// @dev Open a lot, fund a ceiling (bid intent) but place no bid, and stake an operator bond for the
    ///      session. Returns the lot's endsAt.
    function _openFundedUnbidLot(uint256 lotId) private returns (uint64 endsAt) {
        _init(address(0));
        endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        auction.openLot(lotId, seller, RESERVE_PRICE, endsAt);
        vm.deal(bidder1, 10 ether);
        vm.prank(bidder1);
        auction.depositCeiling{value: 5 ether}(lotId, 5 ether); // funded bid-intent, never bid
        vm.deal(operator1, 4 ether);
        vm.prank(operator1);
        operatorBond.deposit{value: 4 ether}(SESSION_ID, address(auction), 4 ether);
    }

    /// Arbiter slashes a funded, zero-bid lot; the whole operator pool routes to Treasury at settle,
    /// and the funded principal still reclaims its ceiling (the void strands no funds).
    function test_NonLivenessSlashByArbiter() public {
        uint256 lotId = 7;
        uint64 endsAt = _openFundedUnbidLot(lotId);

        vm.warp(uint256(endsAt) + DISPUTE_WINDOW_SEC + 1); // auction window + grace
        vm.expectEmit(true, false, false, false, address(auction));
        emit ISessionAuction.LotNonLivenessSlashed(lotId);
        vm.prank(arbiter);
        auction.slashNonLivenessForLot(lotId);
        assertEq(uint8(auction.getLot(lotId).phase), uint8(LotPhase.Voided), "lot voided on non-liveness slash");

        // The flag routes the WHOLE pool to Treasury at settle (no specific victim).
        vm.warp(auction.bondClaimsCloseAt() + 1);
        operatorBond.closeSession(SESSION_ID, address(auction));
        uint256 treasuryBefore = address(treasury).balance;
        operatorBond.settleSlash(SESSION_ID);
        assertEq(address(treasury).balance - treasuryBefore, 4 ether, "whole operator pool to Treasury");

        // The funded principal still reclaims its ceiling deposit (no funds stranded by the void).
        uint256 b1 = bidder1.balance;
        vm.prank(bidder1);
        auction.withdrawDeposit(lotId, 5 ether);
        assertEq(bidder1.balance - b1, 5 ether, "funded principal reclaims its deposit after the void");
    }

    /// Guard: a lot that received a BID can NEVER be slashed (operators were demonstrably live).
    function test_RevertWhen_NonLivenessSlashOnBidLot() public {
        _bootstrapHammeredLot(); // LOT_ID got real bids + was hammered
        vm.warp(block.timestamp + DISPUTE_WINDOW_SEC + 1);
        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.NotNonLive.selector);
        auction.slashNonLivenessForLot(LOT_ID);
    }

    /// Guard: before the auction-window + grace elapses, the slash reverts (operators still have time).
    function test_RevertWhen_NonLivenessSlashBeforeGrace() public {
        uint256 lotId = 8;
        uint64 endsAt = _openFundedUnbidLot(lotId);
        vm.warp(uint256(endsAt) + 1); // past endsAt but within the grace
        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.WindowOpen.selector);
        auction.slashNonLivenessForLot(lotId);
    }

    /// Guard: a lot with NO funded deposit can never be slashed (no bid-intent -> just no interest).
    function test_RevertWhen_NonLivenessSlashUnfundedLot() public {
        _init(address(0));
        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        auction.openLot(9, seller, RESERVE_PRICE, endsAt);
        vm.warp(uint256(endsAt) + DISPUTE_WINDOW_SEC + 1);
        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.NotNonLive.selector);
        auction.slashNonLivenessForLot(9);
    }

    /// Guard: a sub-reserve deposit is not bid-capable funded intent, so the lot stays unslashable.
    /// Only a ceiling that reaches the reserve counts; a bidder who could never have cleared BidTooLow
    /// is not evidence the operators went dark.
    function test_RevertWhen_NonLivenessSlashSubReserveOnly() public {
        _init(address(0));
        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        auction.openLot(11, seller, RESERVE_PRICE, endsAt);
        vm.deal(bidder1, 1 ether);
        vm.prank(bidder1);
        auction.depositCeiling{value: RESERVE_PRICE - 1}(11, RESERVE_PRICE - 1); // sub-reserve: not bid-capable
        vm.warp(uint256(endsAt) + DISPUTE_WINDOW_SEC + 1);
        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.NotNonLive.selector);
        auction.slashNonLivenessForLot(11);
    }

    /// Guard: only the arbiter may trigger the non-liveness slash.
    function test_RevertWhen_NonLivenessSlashNotArbiter() public {
        uint256 lotId = 10;
        uint64 endsAt = _openFundedUnbidLot(lotId);
        vm.warp(uint256(endsAt) + DISPUTE_WINDOW_SEC + 1);
        vm.prank(bidder3);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.slashNonLivenessForLot(lotId);
    }

    // challengeOverCeiling revert gates, mutating one condition at a time.

    // (a) caller != recorded _bidOf principal -> NotPrincipal.
    function test_RevertWhen_ChallengeOverCeilingNotPrincipal() public {
        _bootstrapHammeredLot();

        // bidder3 is not the principal recorded at seq 1 (that is bidder1).
        vm.prank(bidder3);
        vm.expectRevert(ISessionAuction.NotPrincipal.selector);
        auction.challengeOverCeiling(LOT_ID, 1, OVER_MAXBID, OVER_SALT);
    }

    // (b) wrong (maxBid, salt) for the stored commitment -> CommitmentMismatch.
    function test_RevertWhen_ChallengeOverCeilingMismatch() public {
        _bootstrapHammeredLot();

        // Right principal, but a salt that does not open the stored commitment.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.CommitmentMismatch.selector);
        auction.challengeOverCeiling(LOT_ID, 1, OVER_MAXBID, keccak256("WRONG_SALT"));
    }

    // (c) bidAmount == maxBid is on-policy (at-ceiling), not over-ceiling -> NotOverCeiling.
    //     The on-chain check is strictly bidAmount > maxBid, never bidAmount != maxBid.
    function test_RevertWhen_AtCeilingNotOverCeiling() public {
        // A lot whose winning seq lands exactly at its committed ceiling: amount == maxBid, so the
        // commitment opens cleanly (no CommitmentMismatch) and the strict bidAmount > maxBid check is
        // false. At-ceiling clearing is on-policy, not fraud.
        uint256 lotId = 2;
        uint128 atCeiling = WINNER_AMOUNT; // committed maxBid == landed amount
        _init(address(0));
        vm.prank(address(hammer));
        auction.openLot(lotId, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));
        // seq 1: a lower losing bid (over its own ceiling, but irrelevant here) so seq 2 wins.
        _depositAndBid(lotId, bidder1, 0, 0, OVER_AMOUNT, OVER_MAXBID, OVER_SALT, keccak256(abi.encode("AC1", lotId)));
        // seq 2: bidder2 lands AT its ceiling (amount == maxBid == atCeiling), committed under WINNER_SALT.
        _depositAndBid(lotId, bidder2, OVER_AMOUNT, 0, atCeiling, atCeiling, WINNER_SALT, keccak256(abi.encode("AC2", lotId)));
        vm.warp(block.timestamp + 1 days + 1);
        auction.hammer(lotId);

        // Opening seq 2 with (atCeiling, WINNER_SALT) matches the stored commitment, and
        // bidAmount == maxBid, so it must revert NotOverCeiling (not CommitmentMismatch).
        vm.prank(bidder2);
        vm.expectRevert(ISessionAuction.NotOverCeiling.selector);
        auction.challengeOverCeiling(lotId, 2, atCeiling, WINNER_SALT);
    }

    // Class B challengeAttestation: posts a refundable bond, opens a gated dispute, one open
    // dispute per seq.

    // Happy: bond pulled, bidIntegrityOpen++, record written, Opened(class=1, bond>0), gate set.
    function test_ChallengeAttestationOpensBondedDispute() public {
        _bootstrapHammeredLot();

        uint64 seq = 2; // the winning seq carries the (alleged) faulty attestation
        uint256 clonePre = address(auction).balance;
        uint256 challengerPre = bidder3.balance;

        // Permissionless to FILE: bidder3 is not a party, just a keeper posting evidence + bond.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityDisputeOpened(LOT_ID, seq, bidder3, 1, INTEGRITY_BOND_AMT);

        vm.prank(bidder3);
        auction.challengeAttestation{value: INTEGRITY_BOND_AMT}(LOT_ID, seq, hex"deadbeef");

        // The gate now blocks the seller-paying release until the dispute is resolved.
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 1, "Class B increments the gate");
        assertTrue(auction.bidIntegrityDisputeOpen(LOT_ID), "Class B opens the release gate");

        // Bond conservation: the clone holds the bond, the challenger is debited exactly it.
        assertEq(address(auction).balance, clonePre + INTEGRITY_BOND_AMT, "clone holds the Class B bond");
        assertEq(bidder3.balance, challengerPre - INTEGRITY_BOND_AMT, "challenger debited the bond");
    }

    // A second challengeAttestation on the same already-open seq reverts AlreadyDisputed.
    function test_RevertWhen_ChallengeAttestationDoubleOpen() public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 2, bidder3);

        // The AlreadyDisputed check fires before any bond is pulled (one open Class B dispute per
        // seq). Snapshot the single-open state, the would-be second filer's balance, and the clone
        // balance so the counter-stays-1 assertion pins that the second file neither advanced the gate
        // to 2 nor pulled a second bond.
        uint8 gatePre = auction.getLot(LOT_ID).bidIntegrityOpen;
        assertEq(gatePre, 1, "exactly one Class B dispute is open before the double-file");
        uint256 clonePre = address(auction).balance;
        uint256 secondFilerPre = bidder1.balance; // a different filer than the original challenger bidder3

        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.AlreadyDisputed.selector);
        auction.challengeAttestation{value: INTEGRITY_BOND_AMT}(LOT_ID, 2, hex"deadbeef");

        // The gate did not advance to 2 (the second file was rejected on the open-flag, not opened), and
        // no second bond was pulled into the clone nor debited from the would-be second filer.
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 1, "double-open must leave the counter at 1, not advance to 2");
        assertEq(address(auction).balance, clonePre, "double-open must not pull a second bond into the clone");
        assertEq(bidder1.balance, secondFilerPre, "double-open must not debit the second filer's bond");
    }

    // Re-opening the same seq after resolution. AlreadyDisputed is keyed on IntegrityDispute.open ==
    // true, not on a sticky record-existence flag; resolve/timeout clear `open` and decrement
    // bidIntegrityOpen. So a second challengeAttestation on the same seq after the first resolves is
    // allowed: it re-increments the gate 0 -> 1 and re-freezes release (re-file griefing is bounded
    // each round by the refundable bond + permissionless timeout). Drives two full open->resolved
    // cycles on one seq, pinning that the re-file is not bricked by AlreadyDisputed, the second
    // dispute re-freezes release, and the second resolve returns the uint8 counter to 0 without
    // underflow.
    function test_ChallengeAttestationReopenAfterResolved() public {
        // Delivered native lot so the seller-paying confirmReceipt release path is reachable between
        // dispute cycles (a reject leaves the lot Delivered, not settled).
        SessionAuction a = _freshDeliveredLot(address(0), seller);

        uint256 sellerStart = seller.balance;

        // --- Cycle 1: open Class B on the winning seq 2, reject it (gate 1 -> 0). ---
        _openClassBOn(a, address(0), LOT_ID, 2, bidder3);
        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 1, "cycle 1 open sets the gate to 1");

        vm.prank(arbiter);
        a.resolveBidIntegrityDispute(LOT_ID, 2, false, 0); // reject: pays seller the bond, clears open
        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "cycle 1 reject clears the gate to 0");
        assertFalse(a.bidIntegrityDisputeOpen(LOT_ID), "cycle 1 reject leaves the release gate clean");
        assertEq(seller.balance, sellerStart + INTEGRITY_BOND_AMT, "cycle 1 reject paid the seller one bond");

        // --- Re-file: challengeAttestation on the same seq 2 succeeds (no AlreadyDisputed). ---
        // A different challenger (bidder1) re-opens the dispute, re-pulls a fresh bond, emits Opened
        // again. The open-flag was cleared by the cycle-1 reject, so the already-open check does not fire.
        uint256 cloneBeforeRefile = address(a).balance;
        uint256 refilerBefore = bidder1.balance;

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.BidIntegrityDisputeOpened(LOT_ID, 2, bidder1, 1, INTEGRITY_BOND_AMT);

        vm.prank(bidder1);
        a.challengeAttestation{value: INTEGRITY_BOND_AMT}(LOT_ID, 2, hex"deadbeef");

        // The re-file re-armed the gate 0 -> 1 and pulled exactly one fresh bond.
        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 1, "re-file re-increments the gate 0 -> 1 (open-flag, not sticky record)");
        assertTrue(a.bidIntegrityDisputeOpen(LOT_ID), "re-file re-opens the release gate");
        assertEq(address(a).balance, cloneBeforeRefile + INTEGRITY_BOND_AMT, "re-file pulls a fresh bond into the clone");
        assertEq(bidder1.balance, refilerBefore - INTEGRITY_BOND_AMT, "re-filer debited exactly one fresh bond");

        // The re-armed gate AGAIN blocks the seller-paying confirmReceipt release (re-frozen).
        vm.prank(bidder2); // the winner / buyer
        vm.expectRevert(ISessionAuction.BidIntegrityDisputeIsOpen.selector);
        a.confirmReceipt(LOT_ID, keccak256("reopen-photo"), "ipfs://reopen-photo");

        // --- Cycle 2: resolve the second dispute and assert the counter returns to 0 EXACTLY once. ---
        vm.prank(arbiter);
        a.resolveBidIntegrityDispute(LOT_ID, 2, false, 0); // reject again: pays seller the second bond
        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "cycle 2 resolve returns the counter to 0 (no underflow)");
        assertFalse(a.bidIntegrityDisputeOpen(LOT_ID), "cycle 2 resolve clears the release gate again");
        // The counter is exactly 0, not a wrapped uint8 (e.g. 255).
        assertEq(seller.balance, sellerStart + 2 * INTEGRITY_BOND_AMT, "two reject cycles paid the seller exactly two bonds");

        // With both cycles resolved, the seller-paying release now succeeds (the gate is durably clear).
        vm.prank(bidder2);
        a.confirmReceipt(LOT_ID, keccak256("reopen-photo"), "ipfs://reopen-photo");
        assertEq(uint8(a.getLot(LOT_ID).phase), uint8(LotPhase.Settled), "release succeeds after both re-file cycles resolved");
    }

    // resolveBidIntegrityDispute (onlyArbiter): the only decrement-by-decision.

    // (a) non-arbiter caller -> Unauthorized.
    function test_RevertWhen_ResolveIntegrityNotArbiter() public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 2, bidder3);

        // bidder3 (the challenger) is not the arbiter.
        vm.prank(bidder3);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.resolveBidIntegrityDispute(LOT_ID, 2, true, 0);
    }

    // (b) upheld == true: records harm, refunds the challenger bond, emits ClaimUpheld, clears
    //     the gate (bidIntegrityOpen--).
    function test_ResolveIntegrityUpheld() public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 2, bidder3);

        uint128 provenHarm = 1 ether;
        uint256 challengerPre = bidder3.balance; // bond was already debited at open
        uint256 sellerPre = seller.balance;
        uint256 clonePre = address(auction).balance;             // clone holds the bond pre-resolve
        uint128 escrowPre = auction.getLot(LOT_ID).escrowAmount;  // winner escrow, must be untouched

        // The arbiter-supplied provenHarm flows to both the event and the bond ledger: assert
        // recordClaim(sessionId, victim == seq-2 principal bidder2, provenHarm) carries the same value
        // the arbiter passed, not just that the event echoes it.
        _mockRecordClaim();
        vm.expectCall(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder2, provenHarm))
        );

        // Upheld: the challenger (bidder3) gets its bond back; harm recorded to the victim.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityClaimUpheld(LOT_ID, 2, bidder2, provenHarm);

        vm.prank(arbiter);
        auction.resolveBidIntegrityDispute(LOT_ID, 2, true, provenHarm);

        // Gate cleared so release can proceed.
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "uphold decrements the gate");
        assertFalse(auction.bidIntegrityDisputeOpen(LOT_ID), "uphold clears the release gate");

        // Bond refunded to the challenger; the seller is untouched on an uphold.
        assertEq(bidder3.balance, challengerPre + INTEGRITY_BOND_AMT, "uphold refunds challenger bond");
        assertEq(seller.balance, sellerPre, "uphold does not pay the seller");

        // Bond-pool isolation: exactly the bond left the clone and the winner escrowAmount is
        // unchanged, so a refund funded from escrow (or any other bucket) is caught.
        assertEq(address(auction).balance, clonePre - INTEGRITY_BOND_AMT, "exactly the bond left the clone");
        assertEq(auction.getLot(LOT_ID).escrowAmount, escrowPre, "uphold must not touch the winner escrow");
    }

    // (c) upheld == false: bond goes to the seller, emits Rejected(byTimeout=false), clears the gate.
    function test_ResolveIntegrityRejected() public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 2, bidder3);

        uint256 sellerPre = seller.balance;
        uint256 challengerPre = bidder3.balance;
        uint256 clonePre = address(auction).balance;             // clone holds the bond pre-resolve
        uint128 escrowPre = auction.getLot(LOT_ID).escrowAmount;  // winner escrow, must be untouched

        // Only an uphold calls recordClaim; a reject pays the bond to the seller and records no harm.
        // Mock recordClaim (so a stray call would not revert), pass a nonzero provenHarm to prove the
        // `upheld` flag (not the harm value) gates the write, and assert the selector fires exactly
        // zero times across the reject.
        _mockRecordClaim();
        vm.expectCall(address(operatorBond), abi.encodeWithSelector(IOperatorBond.recordClaim.selector), 0);

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityDisputeRejected(LOT_ID, 2, false); // arbiter reject, not a timeout

        // Nonzero provenHarm on the reject: the upheld==false branch must record nothing regardless.
        vm.prank(arbiter);
        auction.resolveBidIntegrityDispute(LOT_ID, 2, false, 1 ether);

        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "reject decrements the gate");
        assertFalse(auction.bidIntegrityDisputeOpen(LOT_ID), "reject clears the release gate");

        // The griefed seller gets the bond; the rejected challenger recovers nothing.
        assertEq(seller.balance, sellerPre + INTEGRITY_BOND_AMT, "reject pays the bond to the seller");
        assertEq(bidder3.balance, challengerPre, "rejected challenger does not recover the bond");

        // Bond-pool isolation: exactly the bond left the clone to fund the seller payout and the
        // winner escrow is unchanged, so a seller paid out of escrowAmount is caught.
        assertEq(address(auction).balance, clonePre - INTEGRITY_BOND_AMT, "exactly the bond left the clone on reject");
        assertEq(auction.getLot(LOT_ID).escrowAmount, escrowPre, "reject must not touch the winner escrow");
    }

    // timeoutBidIntegrityDispute (permissionless anti-censorship).

    // (a) before openedAt + _integrityTimeoutSec -> WindowOpen.
    function test_RevertWhen_TimeoutBeforeWindow() public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 2, bidder3);

        // One second before the timeout elapses.
        vm.warp(block.timestamp + INTEGRITY_TIMEOUT_SEC - 1);

        vm.prank(bidder1); // permissionless: any caller
        vm.expectRevert(ISessionAuction.WindowOpen.selector);
        auction.timeoutBidIntegrityDispute(LOT_ID, 2);

        // The arbiter cannot shortcut the window via the timeout entrypoint either: timeout is the
        // anti-censorship backstop, not a second arbiter resolve path, so it stays WindowOpen even for
        // the arbiter (who resolves early only via resolveBidIntegrityDispute).
        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.WindowOpen.selector);
        auction.timeoutBidIntegrityDispute(LOT_ID, 2);
    }

    // (b) at/after the timeout: resolves AGAINST the silent challenger (bond to seller), clears
    //     the gate, emits Rejected(byTimeout=true). Permissionless caller.
    function test_TimeoutResolvesAgainstSilentChallenger() public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 2, bidder3);

        uint256 sellerPre = seller.balance;
        uint256 challengerPre = bidder3.balance;
        uint256 clonePre = address(auction).balance;             // clone holds the bond pre-timeout
        uint128 escrowPre = auction.getLot(LOT_ID).escrowAmount;  // winner escrow, MUST be untouched

        // A timeout resolves against the silent challenger (bond to the seller) and records no harm;
        // only an uphold calls recordClaim. Mock it and assert the selector fires exactly zero times
        // (recording harm on a timeout would slash the operator bond for a dispute that was never
        // substantiated).
        _mockRecordClaim();
        vm.expectCall(address(operatorBond), abi.encodeWithSelector(IOperatorBond.recordClaim.selector), 0);

        vm.warp(block.timestamp + INTEGRITY_TIMEOUT_SEC); // boundary: callable exactly at the timeout

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityDisputeRejected(LOT_ID, 2, true); // byTimeout == true

        vm.prank(bidder1); // not the arbiter, not a party: the liveness backstop is permissionless
        auction.timeoutBidIntegrityDispute(LOT_ID, 2);

        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "timeout decrements the gate");
        assertFalse(auction.bidIntegrityDisputeOpen(LOT_ID), "timeout clears the release gate");

        // Resolves against the silent challenger: the seller takes the bond.
        assertEq(seller.balance, sellerPre + INTEGRITY_BOND_AMT, "timeout pays the bond to the seller");
        assertEq(bidder3.balance, challengerPre, "silent challenger forfeits the bond on timeout");

        // Bond-pool isolation: exactly the bond left the clone, winner escrow unchanged, so the
        // permissionless timeout payout is not funded from escrowAmount.
        assertEq(address(auction).balance, clonePre - INTEGRITY_BOND_AMT, "exactly the bond left the clone on timeout");
        assertEq(auction.getLot(LOT_ID).escrowAmount, escrowPre, "timeout must not touch the winner escrow");
    }

    // (b-void) Under a session void a silent Class B timeout is not the challenger's fault (the whole
    //          lot is unwound, the challenged bid refunded), so the bond returns to the challenger,
    //          not the seller (a seller who is no longer being paid).
    function test_TimeoutUnderVoidRefundsChallenger() public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 2, bidder3);

        // House voids the whole session (cfg.hammer == the factory, onlyHammer).
        vm.prank(address(hammer));
        auction.voidSession("operator incident");

        uint256 sellerPre = seller.balance;
        uint256 challengerPre = bidder3.balance;
        uint256 clonePre = address(auction).balance;

        // A timeout records NO harm even under a void (only an uphold calls recordClaim); pin it to zero.
        _mockRecordClaim();
        vm.expectCall(address(operatorBond), abi.encodeWithSelector(IOperatorBond.recordClaim.selector), 0);

        vm.warp(block.timestamp + INTEGRITY_TIMEOUT_SEC); // boundary: callable exactly at the timeout

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityDisputeRejected(LOT_ID, 2, true); // byTimeout == true

        vm.prank(bidder1); // permissionless backstop
        auction.timeoutBidIntegrityDispute(LOT_ID, 2);

        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "timeout clears the gate under a void too");
        // No strand: the challenger reclaims the full bond; the seller takes nothing under a void.
        assertEq(bidder3.balance, challengerPre + INTEGRITY_BOND_AMT, "void timeout refunds the challenger, not the seller");
        assertEq(seller.balance, sellerPre, "seller takes nothing on a void timeout");
        assertEq(address(auction).balance, clonePre - INTEGRITY_BOND_AMT, "exactly the bond left the clone");
    }

    // (c) the seq is Class A (or not open) -> WrongDeliveryState. Class A never sets the gate,
    //     so there is nothing for the timeout to clear.
    function test_RevertWhen_TimeoutOnClassA() public {
        _bootstrapHammeredLot();

        // No Class B dispute was opened on seq 1; a Class A claim writes no IntegrityDispute.
        // Even past the timeout horizon, the timeout has nothing open+Class-B to resolve.
        vm.warp(block.timestamp + INTEGRITY_TIMEOUT_SEC + 1);

        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.timeoutBidIntegrityDispute(LOT_ID, 1);
    }

    // Release-gating boundary: Class A never freezes release; only Class B sets the gate that blocks
    // the seller-paying release until resolved.
    function test_ClassANeverFreezesRelease_ClassBDoes() public {
        _bootstrapHammeredLot();

        // Drive the winner to a finalized, delivered state (the release point).
        vm.warp(block.timestamp + AC_CHALLENGE_SEC); // close the anti-collusion window
        auction.finalizeWinner(LOT_ID);
        vm.prank(seller);
        auction.markDelivered(LOT_ID, keccak256("delivery-proof"), "ipfs://delivery");

        // (a) A Class A claim on the LOSING seq records harm but leaves the gate untouched, so a
        //     buyer confirmReceipt (a seller-paying _release) is NOT blocked by it.
        vm.prank(bidder1);
        auction.challengeOverCeiling(LOT_ID, 1, OVER_MAXBID, OVER_SALT);
        assertFalse(auction.bidIntegrityDisputeOpen(LOT_ID), "Class A leaves the release gate clean");

        // The winner can still confirm and release to the seller (Class A is not a freeze).
        vm.prank(bidder2);
        auction.confirmReceipt(LOT_ID, keccak256("photo"), "ipfs://photo");
        Lot memory afterRelease = auction.getLot(LOT_ID);
        assertEq(uint8(afterRelease.phase), uint8(LotPhase.Settled), "Class A does not block release");
        assertEq(uint8(afterRelease.deliveryState), uint8(DeliveryState.Released), "released past Class A");

        // (b) A Class B challengeAttestation does set the gate and blocks the seller-paying release
        //     path with BidIntegrityDisputeIsOpen. Use a second lot on the same session (LOT_ID is now
        //     Settled) so the gate boundary is exercised on a fresh delivered lot.
        uint256 lot2 = 3;
        _bootstrapHammeredLotId(lot2);
        vm.warp(block.timestamp + AC_CHALLENGE_SEC);
        auction.finalizeWinner(lot2);
        vm.prank(seller);
        auction.markDelivered(lot2, keccak256("delivery-proof-2"), "ipfs://delivery2");

        _openClassB(lot2, 2, bidder3);
        assertTrue(auction.bidIntegrityDisputeOpen(lot2), "Class B sets the release gate");

        // The gate blocks the BUYER-driven seller-paying release (confirmReceipt)...
        vm.prank(bidder2);
        vm.expectRevert(ISessionAuction.BidIntegrityDisputeIsOpen.selector);
        auction.confirmReceipt(lot2, keccak256("photo-2"), "ipfs://photo2");

        // ...and the permissionless seller-paying release path (releaseAfterWindow): both
        // seller-paying entrypoints must be frozen by the same Class B counter. Warp past the dispute
        // window so only the integrity gate, not a timing guard, blocks it.
        Lot memory delivered2 = auction.getLot(lot2);
        vm.warp(uint256(delivered2.deliveredAt) + DISPUTE_WINDOW_SEC + 1);
        vm.expectRevert(ISessionAuction.BidIntegrityDisputeIsOpen.selector);
        auction.releaseAfterWindow(lot2);
    }

    // Asymmetric gate, buyer-refund half. An open Class B challengeAttestation freezes only the
    // seller-paying release exits (confirmReceipt, releaseAfterWindow, resolveDispute(ReleaseToSeller)).
    // It does not gate _refund, reclaimUndelivered, or resolveDispute(RefundToBuyer), so the buyer's
    // no-strand exits stay reachable while a Class B dispute is open (over-gating would trap the winner
    // escrow behind a censoring/absent arbiter). Drive a lot to Awaiting but not delivered, open a live
    // Class B dispute, then reclaim: it succeeds without resolving the dispute, and the gate stays open
    // across the refund.
    function test_ClassBDoesNotBlockBuyerRefund() public {
        _bootstrapHammeredLot();

        // finalizeWinner is itself gated on !bidIntegrityDisputeOpen, so it must run BEFORE the Class B
        // dispute opens: close the AC window, finalize to Awaiting (sets awaitingAt), and deliberately
        // do NOT markDelivered (the seller-never-delivers strand).
        vm.warp(block.timestamp + AC_CHALLENGE_SEC);
        auction.finalizeWinner(LOT_ID);
        Lot memory awaiting = auction.getLot(LOT_ID);
        assertEq(uint8(awaiting.phase), uint8(LotPhase.Awaiting), "lot is Awaiting (finalized, not delivered)");
        assertEq(
            uint8(awaiting.deliveryState),
            uint8(DeliveryState.AwaitingDelivery),
            "deliveryState AwaitingDelivery (no markDelivered)"
        );

        // Open a live Class B dispute on the winning seq: the gate is now set (bidIntegrityDisputeOpen).
        _openClassB(LOT_ID, 2, bidder3);
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 1, "Class B set the integrity gate (open == 1)");
        assertTrue(auction.bidIntegrityDisputeOpen(LOT_ID), "the release gate is open during the refund");

        // Before the seller-deliver deadline, reclaimUndelivered reverts on the timing guard
        // (DeliveryWindowNotElapsed), not the integrity gate: an over-gating SUT would revert
        // BidIntegrityDisputeIsOpen even before the deadline.
        vm.prank(bidder2); // the highBidder / buyer
        vm.expectRevert(ISessionAuction.DeliveryWindowNotElapsed.selector);
        auction.reclaimUndelivered(LOT_ID);

        // Warp to exactly awaitingAt + _sellerDeliverSec: the reclaim boundary.
        vm.warp(uint256(awaiting.awaitingAt) + SELLER_DELIVER_SEC);

        // Conservation surface across the reclaim: the buyer (bidder2) receives the full winner escrow
        // with no fee (it routes through _refund), exactly the escrow leaves the clone, and the gate is
        // not cleared by the refund.
        uint128 escrowPre = auction.getLot(LOT_ID).escrowAmount;
        assertEq(escrowPre, WINNER_AMOUNT, "winner escrow == the committed winning amount");
        uint256 buyerPre = bidder2.balance;
        uint256 clonePre = address(auction).balance;
        uint8 gatePre = auction.getLot(LOT_ID).bidIntegrityOpen;
        assertEq(gatePre, 1, "the Class B gate is still open at the reclaim instant");

        // reclaimUndelivered emits ReclaimedUndelivered(lot, buyer, escrow) then routes through _refund,
        // which emits Refunded(lot, buyer, escrow): both fire in this order with the full escrow and
        // bidder2 (== highBidder) as recipient, despite the open Class B dispute.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.ReclaimedUndelivered(LOT_ID, bidder2, escrowPre);
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Refunded(LOT_ID, bidder2, uint256(escrowPre));

        vm.prank(bidder2); // onlyBuyer == the winner / highBidder
        auction.reclaimUndelivered(LOT_ID);

        // Terminal refund post-state: phase Refunded, deliveryState Refunded, escrow 0.
        Lot memory refunded = auction.getLot(LOT_ID);
        assertEq(uint8(refunded.phase), uint8(LotPhase.Refunded), "Class B did not block the buyer refund: phase Refunded");
        assertEq(uint8(refunded.deliveryState), uint8(DeliveryState.Refunded), "deliveryState Refunded after reclaim");
        assertEq(refunded.escrowAmount, 0, "escrow zeroed on refund (no-double-pay)");

        // Conservation: the buyer got the full escrow (no fee skimmed) and exactly the escrow left the
        // clone, so a fee taken on the refund path (treating it as a sale) is caught.
        assertEq(bidder2.balance - buyerPre, uint256(escrowPre), "buyer received the FULL escrow, no fee");
        assertEq(clonePre - address(auction).balance, uint256(escrowPre), "exactly the escrow left the clone");

        // The asymmetry: the Class B gate is still open after the refund (the refund neither cleared it
        // nor was predicated on clearing it), so _refund / reclaimUndelivered are not gated by the Class
        // B counter.
        assertEq(refunded.bidIntegrityOpen, 1, "the Class B gate stays open across the refund (not cleared by it)");
        assertTrue(auction.bidIntegrityDisputeOpen(LOT_ID), "Class B dispute still open after the buyer's refund exit");
    }

    // Harm-ledger no-double-record. A Class A claim on a seq records harm into the bond once; a later
    // Class B uphold on the same seq must not record it a second time (harm is recorded only if not
    // already recorded for the seq).
    function test_ClassAThenClassBNoDoubleRecord() public {
        _bootstrapHammeredLot();
        _mockRecordClaim();

        uint128 expectedHarm = OVER_AMOUNT - OVER_MAXBID;

        // recordClaim fires exactly once (the Class A record) with the Class A args. vm.expectCall
        // counts span the whole test, so a Class B uphold on the same seq that wrongly re-recorded
        // would push the selector total to 2 and fail. Pins "recorded once".
        vm.expectCall(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder1, expectedHarm)),
            1
        );
        vm.expectCall(address(operatorBond), abi.encodeWithSelector(IOperatorBond.recordClaim.selector), 1);

        // Class A on seq 1 records harm once (victim bidder1).
        vm.prank(bidder1);
        auction.challengeOverCeiling(LOT_ID, 1, OVER_MAXBID, OVER_SALT);

        // Open a Class B on the same seq 1 and uphold it. seq 1 harm is already recorded, so the
        // resolve must not call recordClaim again (enforced by the count-1 assertions above); it still
        // refunds the challenger bond and clears the gate.
        _openClassB(LOT_ID, 1, bidder3);
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 1, "Class B on seq 1 sets the gate");

        vm.prank(arbiter);
        auction.resolveBidIntegrityDispute(LOT_ID, 1, true, expectedHarm);

        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "Class B uphold clears the gate");
    }

    // challengeOverCeiling on empty and below-ceiling seqs.

    // Probe a never-placed seq: the stored bid principal is address(0), so msg.sender (never
    // address(0)) is not the recorded principal -> NotPrincipal (the zero-principal empty-slot
    // branch, distinct from the wrong-bidder case).
    function test_RevertWhen_ChallengeOverCeilingUnknownSeq() public {
        _bootstrapHammeredLot();

        // seq 999 was never placed; its stored principal is address(0).
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.NotPrincipal.selector);
        auction.challengeOverCeiling(LOT_ID, 999, OVER_MAXBID, OVER_SALT);
    }

    // The winning on-policy seq (seq 2) opened with its true (maxBid, salt): the commitment opens
    // cleanly (no CommitmentMismatch) but WINNER_AMOUNT < WINNER_MAXBID, so the strict bidAmount >
    // maxBid check is false -> NotOverCeiling. Covers the below-ceiling branch that
    // test_RevertWhen_AtCeilingNotOverCeiling (the equal case) does not.
    function test_RevertWhen_ChallengeWinningOnPolicySeqNotOver() public {
        _bootstrapHammeredLot();

        vm.prank(bidder2); // the recorded principal of the winning seq 2
        vm.expectRevert(ISessionAuction.NotOverCeiling.selector);
        auction.challengeOverCeiling(LOT_ID, 2, WINNER_MAXBID, WINNER_SALT);
    }

    // Pins the strict bidAmount > maxBid check from the over side at the minimal positive harm. The
    // offending loser seq lands amount == maxBid + 1, so the commitment opens cleanly, the strict >
    // is true at harm 1, and provenHarm must equal bidAmount - maxBid == 1 wei (catching an
    // off-by-one low or high).
    function test_ChallengeOverCeilingOneWeiOver() public {
        uint256 lotId = 10;
        _init(address(0));
        vm.prank(address(hammer));
        auction.openLot(lotId, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));

        // seq 1 (loser): committed maxBid == 1 ether, lands exactly 1 ether + 1 wei (one wei over its own
        // ceiling). prevTop == 0 (first bid); 1 ether + 1 wei >= RESERVE_PRICE clears the reserve.
        _depositAndBid(lotId, bidder1, 0, 0, WONE_AMOUNT, WONE_MAXBID, WONE_SALT, keccak256(abi.encode("WONE_Q1", lotId)));
        // seq 2 (winner): a higher on-policy bid so seq 1 stays a loser. prevTop is seq 1's top
        // (WONE_AMOUNT); WINNER_AMOUNT clears the 2% min increment over it.
        _depositAndBid(lotId, bidder2, WONE_AMOUNT, 0, WINNER_AMOUNT, WINNER_MAXBID, WINNER_SALT, keccak256(abi.encode("WONE_Q2", lotId)));

        vm.warp(block.timestamp + 1 days + 1);
        auction.hammer(lotId);

        // provenHarm at the minimal positive value: exactly one wei, == bidAmount - maxBid.
        uint128 expectedHarm = WONE_AMOUNT - WONE_MAXBID; // == 1 wei
        assertEq(expectedHarm, 1, "fixture sanity: the over-ceiling margin is exactly one wei");

        _mockRecordClaim();
        // The harm written to the bond ledger is exactly 1 (not 0 from an off-by-one >=, not 2 from a +1).
        vm.expectCall(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder1, uint128(1)))
        );
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityDisputeOpened(lotId, 1, bidder1, 0, 0); // Class A: class 0, bond 0
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityClaimUpheld(lotId, 1, bidder1, 1); // harm pinned to 1 wei exactly

        // Conservation: the minimal-harm self-proving call is still a pure external-ledger write (no
        // clone money moves), same isolation as the larger-gap Class A tests.
        uint256 clonePre = address(auction).balance;
        uint128 escrowPre = auction.getLot(lotId).escrowAmount;

        vm.prank(bidder1); // the recorded principal of the one-wei-over loser seq
        auction.challengeOverCeiling(lotId, 1, WONE_MAXBID, WONE_SALT);

        // Succeeded (over-ceiling at harm 1): the gate stays clean and no clone money moved.
        assertEq(auction.getLot(lotId).bidIntegrityOpen, 0, "one-wei-over Class A must not set the gate");
        assertFalse(auction.bidIntegrityDisputeOpen(lotId), "one-wei-over Class A never opens the release gate");
        assertEq(address(auction).balance, clonePre, "one-wei-over Class A must move no clone funds");
        assertEq(auction.getLot(lotId).escrowAmount, escrowPre, "one-wei-over Class A must not touch the winner escrow");
    }

    // challengeAttestation bond intake fails closed. It pulls _integrityBondAmt via _pull; on the
    // native rail it asserts msg.value == _integrityBondAmt -> WrongBond, so an under or over payment
    // fails closed: no dispute opened, no gate increment, bond not pulled.
    function test_RevertWhen_ChallengeAttestationWrongBondNative() public {
        _bootstrapHammeredLot();

        // (a) underpay
        vm.prank(bidder3);
        vm.expectRevert(ISessionAuction.WrongBond.selector);
        auction.challengeAttestation{value: INTEGRITY_BOND_AMT - 1}(LOT_ID, 2, hex"deadbeef");

        // (b) overpay
        vm.prank(bidder3);
        vm.expectRevert(ISessionAuction.WrongBond.selector);
        auction.challengeAttestation{value: INTEGRITY_BOND_AMT + 1}(LOT_ID, 2, hex"deadbeef");

        // Fails closed in both: the gate is untouched.
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "wrong-bond must not open a dispute");
    }

    // ERC-20 rail: challengeAttestation MUST carry msg.value == 0 (pull is via safeTransferFrom);
    // sending wei reverts WrongBond even with a valid approval. Fails closed.
    function test_RevertWhen_ChallengeAttestationWrongBondERC20() public {
        SessionAuction a = _freshDeliveredLot(address(token), seller);

        fundToken(bidder3, INTEGRITY_BOND_AMT);
        vm.prank(bidder3);
        token.approve(address(a), INTEGRITY_BOND_AMT);

        vm.prank(bidder3);
        vm.expectRevert(ISessionAuction.WrongBond.selector);
        a.challengeAttestation{value: 1 wei}(LOT_ID, 2, hex"deadbeef");

        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "ERC-20 wrong-bond must not open a dispute");
    }

    // Class B evidence (failed P256.verify / high-S / wrong MRENCLAVE / skipped increment) can
    // attach to any landed bid, not only the winner. Open a Class B on the losing seq 1 and assert
    // it opens (bond pulled, gate++, event class == 1).
    function test_ChallengeAttestationOnLosingSeq() public {
        _bootstrapHammeredLot();

        uint256 clonePre = address(auction).balance;
        uint256 challengerPre = bidder3.balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityDisputeOpened(LOT_ID, 1, bidder3, 1, INTEGRITY_BOND_AMT);

        vm.prank(bidder3);
        auction.challengeAttestation{value: INTEGRITY_BOND_AMT}(LOT_ID, 1, hex"deadbeef");

        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 1, "Class B on a loser increments the gate");
        assertTrue(auction.bidIntegrityDisputeOpen(LOT_ID), "Class B on a loser opens the gate");
        assertEq(address(auction).balance, clonePre + INTEGRITY_BOND_AMT, "clone holds the loser-seq bond");
        assertEq(bidder3.balance, challengerPre - INTEGRITY_BOND_AMT, "challenger debited the loser-seq bond");
    }

    // resolveBidIntegrityDispute state guards. It is scoped to an open Class B dispute. An arbiter
    // calling it on a Class A seq (which writes no IntegrityDispute) must revert and must not touch
    // the gate. Seq 1 here had a Class A claim (so harm was recorded) but no open Class B record.
    function test_RevertWhen_ResolveIntegrityOnClassA() public {
        _bootstrapHammeredLot();
        _mockRecordClaim();

        // Self-proving Class A on seq 1: records harm, writes no IntegrityDispute, gate stays 0.
        vm.prank(bidder1);
        auction.challengeOverCeiling(LOT_ID, 1, OVER_MAXBID, OVER_SALT);
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "Class A leaves the gate at 0");

        // The arbiter resolver has nothing OPEN+Class-B to act on at seq 1 -> WrongDeliveryState.
        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.resolveBidIntegrityDispute(LOT_ID, 1, true, 1);

        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "failed resolve must not change the gate");
    }

    // An arbiter resolving the same open Class B dispute twice: the first clears it (gate 1 -> 0),
    // the second must revert (no open record) and must not double-decrement the counter (a uint8 that
    // would underflow / wrap) nor double-pay the bond.
    function test_RevertWhen_ResolveIntegrityDoubleResolve() public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 2, bidder3);

        uint256 sellerPre = seller.balance;

        // Harm suppression across both legs: the first call is a reject (no harm despite a nonzero
        // provenHarm), the second a revert (nothing). Pin the selector at zero calls.
        _mockRecordClaim();
        vm.expectCall(address(operatorBond), abi.encodeWithSelector(IOperatorBond.recordClaim.selector), 0);

        // First resolve (reject) with nonzero harm: pays the seller, clears the gate to 0, records nothing.
        vm.prank(arbiter);
        auction.resolveBidIntegrityDispute(LOT_ID, 2, false, 1 ether);
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "first resolve clears the gate");
        assertEq(seller.balance, sellerPre + INTEGRITY_BOND_AMT, "first resolve pays the bond once");

        // Second resolve on the now-closed dispute reverts; counter stays 0, no second payout.
        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.resolveBidIntegrityDispute(LOT_ID, 2, false, 0);

        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "double-resolve must not change the counter");
        assertEq(seller.balance, sellerPre + INTEGRITY_BOND_AMT, "double-resolve must not pay the bond twice");
    }

    // The arbiter-supplied provenHarm flows verbatim to both the event and recordClaim for any
    // value, including the 0 (uphold-with-no-harm) and type(uint128).max (width) boundaries.
    function testFuzz_ResolveIntegrityUpheldHarm(uint128 h) public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 2, bidder3);
        _mockRecordClaim();

        // The same arbitrary h must reach the bond ledger AND the event (victim == seq-2 bidder2).
        vm.expectCall(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder2, h))
        );
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityClaimUpheld(LOT_ID, 2, bidder2, h);

        vm.prank(arbiter);
        auction.resolveBidIntegrityDispute(LOT_ID, 2, true, h);

        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "uphold clears the gate for any harm");
    }

    // lot.bidIntegrityOpen is a counter, not a bool: two distinct open Class B disputes on one lot
    // raise it to 2, and the seller-paying release stays frozen until both are resolved.
    function test_TwoClassBDisputesGateUntilBothResolved() public {
        SessionAuction a = _freshDeliveredLot(address(0), seller);

        // Two distinct open Class B disputes (seq 1 the loser, seq 2 the winner).
        _openClassBOn(a, address(0), LOT_ID, 1, bidder3);
        _openClassBOn(a, address(0), LOT_ID, 2, bidder1);
        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 2, "two disputes raise the counter to 2");
        assertTrue(a.bidIntegrityDisputeOpen(LOT_ID), "gate true with two open disputes");

        // Resolve seq 1: counter 2 -> 1, gate STILL true; a seller-paying confirmReceipt still blocked.
        vm.prank(arbiter);
        a.resolveBidIntegrityDispute(LOT_ID, 1, false, 0);
        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 1, "one resolved leaves the counter at 1");
        assertTrue(a.bidIntegrityDisputeOpen(LOT_ID), "gate STILL true with one open dispute");

        vm.prank(bidder2);
        vm.expectRevert(ISessionAuction.BidIntegrityDisputeIsOpen.selector);
        a.confirmReceipt(LOT_ID, keccak256("photo"), "ipfs://photo");

        // Resolve seq 2: counter 1 -> 0, gate false; release now succeeds and settles the lot.
        vm.prank(arbiter);
        a.resolveBidIntegrityDispute(LOT_ID, 2, false, 0);
        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "both resolved clears the counter");
        assertFalse(a.bidIntegrityDisputeOpen(LOT_ID), "gate false once both resolved");

        vm.prank(bidder2);
        a.confirmReceipt(LOT_ID, keccak256("photo"), "ipfs://photo");
        assertEq(uint8(a.getLot(LOT_ID).phase), uint8(LotPhase.Settled), "release succeeds after both resolved");
    }

    // A timeout firing on an already-resolved dispute must revert: the arbiter resolved it (open ==
    // false), so there is nothing for the permissionless timeout to clear. Guards a double-decrement.
    function test_RevertWhen_TimeoutAfterArbiterResolved() public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 2, bidder3);

        // Arbiter resolves first (gate 1 -> 0).
        vm.prank(arbiter);
        auction.resolveBidIntegrityDispute(LOT_ID, 2, false, 0);
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "arbiter resolve cleared the gate");

        // Even past the timeout horizon, the now-closed dispute is not timeout-resolvable.
        vm.warp(block.timestamp + INTEGRITY_TIMEOUT_SEC + 1);
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.timeoutBidIntegrityDispute(LOT_ID, 2);

        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "timeout-after-resolve must not change the gate");
    }

    // The arbiter's Class B resolution is bounded by _integrityTimeoutSec. Past the timeout the
    // arbiter can no longer resolve (IntegrityWindowClosed); only the permissionless
    // timeoutBidIntegrityDispute applies (against the challenger, no harm). This caps the latest
    // possible recordClaim at openedAt + _integrityTimeoutSec, which makes the operator bond's
    // closeSession deadline (bondClaimsCloseAt) a sound claim ceiling: no claim lands after operators
    // can withdraw.
    function test_RevertWhen_ArbiterResolvePastTimeout() public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 2, bidder3);

        // Past the timeout horizon the arbiter resolve is rejected (window closed), even an honest one.
        vm.warp(block.timestamp + INTEGRITY_TIMEOUT_SEC + 1);
        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.IntegrityWindowClosed.selector);
        auction.resolveBidIntegrityDispute(LOT_ID, 2, true, 1 ether);

        // The permissionless timeout is the ONLY post-window resolution: clears the gate, bond to seller,
        // no harm recorded. Confirms the dispute still settles (liveness) without an unbounded arbiter.
        uint256 sellerPre = seller.balance;
        auction.timeoutBidIntegrityDispute(LOT_ID, 2);
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "post-window: timeout clears the gate");
        assertEq(seller.balance, sellerPre + INTEGRITY_BOND_AMT, "post-window: bond to seller via timeout");
    }

    // Hostile-seller no-strand on the bond payout. On reject and timeout the bond is _pay'd to the
    // seller. If the seller reverts on receive, _pay credits _pendingWithdrawals (WithdrawalCredited)
    // rather than reverting the resolution, so a hostile seller cannot block the gate-clearing path;
    // claimPending later pulls the parked bond.
    function test_RejectWithHostileSellerParksBond() public {
        F_RejectingReceiver hostileSeller = new F_RejectingReceiver();
        SessionAuction a = _freshDeliveredLot(address(0), address(hostileSeller));
        _openClassBOn(a, address(0), LOT_ID, 2, bidder3);

        // Reject: bond push to the reverting seller fails and is parked, the resolve does NOT revert.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(address(hostileSeller), INTEGRITY_BOND_AMT);

        vm.prank(arbiter);
        a.resolveBidIntegrityDispute(LOT_ID, 2, false, 0);

        // The gate still cleared (liveness preserved despite the hostile seller).
        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "hostile-seller reject still clears the gate");
        assertFalse(a.bidIntegrityDisputeOpen(LOT_ID), "hostile-seller reject clears the release gate");
        assertEq(a.pendingWithdrawal(address(hostileSeller)), INTEGRITY_BOND_AMT, "bond parked to pending");

        // The seller later accepts and pulls the parked bond via claimPending.
        hostileSeller.setReject(false);
        uint256 sellerEthPre = address(hostileSeller).balance;
        vm.prank(address(hostileSeller));
        a.claimPending();
        assertEq(a.pendingWithdrawal(address(hostileSeller)), 0, "pending cleared on claim");
        assertEq(address(hostileSeller).balance - sellerEthPre, INTEGRITY_BOND_AMT, "claim pays the parked bond");
    }

    // Same no-strand property on the PERMISSIONLESS timeout path (the gate-clearing backstop must
    // not be blockable by a hostile seller either).
    function test_TimeoutWithHostileSellerParksBond() public {
        F_RejectingReceiver hostileSeller = new F_RejectingReceiver();
        SessionAuction a = _freshDeliveredLot(address(0), address(hostileSeller));
        _openClassBOn(a, address(0), LOT_ID, 2, bidder3);

        vm.warp(block.timestamp + INTEGRITY_TIMEOUT_SEC);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(address(hostileSeller), INTEGRITY_BOND_AMT);

        vm.prank(bidder1); // permissionless backstop
        a.timeoutBidIntegrityDispute(LOT_ID, 2);

        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "hostile-seller timeout still clears the gate");
        assertFalse(a.bidIntegrityDisputeOpen(LOT_ID), "hostile-seller timeout clears the release gate");
        assertEq(a.pendingWithdrawal(address(hostileSeller)), INTEGRITY_BOND_AMT, "timeout bond parked to pending");
    }

    // The entire bonded Class B lifecycle on the 6-decimal ERC-20 rail (open -> uphold-refund /
    // reject-to-seller / timeout-to-seller). _pull (safeTransferFrom) and _pay (trySafeTransfer)
    // differ from the native push/pull, so the bond accounting is re-validated on token balances.
    function test_ClassBLifecycleERC20_UpheldRefundsChallenger() public {
        SessionAuction a = _freshDeliveredLot(address(token), seller);
        _mockRecordClaim();

        uint256 clonePre = token.balanceOf(address(a));
        _openClassBOn(a, address(token), LOT_ID, 2, bidder3);
        assertEq(token.balanceOf(address(a)), clonePre + INTEGRITY_BOND_AMT, "ERC-20: clone holds the bond");

        uint256 challengerPre = token.balanceOf(bidder3); // bond already debited at open
        uint256 sellerPre = token.balanceOf(seller);

        vm.expectCall(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder2, uint128(1e6)))
        );
        vm.prank(arbiter);
        a.resolveBidIntegrityDispute(LOT_ID, 2, true, uint128(1e6));

        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "ERC-20 uphold clears the gate");
        assertEq(token.balanceOf(bidder3), challengerPre + INTEGRITY_BOND_AMT, "ERC-20 uphold refunds challenger");
        assertEq(token.balanceOf(seller), sellerPre, "ERC-20 uphold does not pay the seller");
    }

    function test_ClassBLifecycleERC20_RejectPaysSeller() public {
        SessionAuction a = _freshDeliveredLot(address(token), seller);
        _openClassBOn(a, address(token), LOT_ID, 2, bidder3);

        uint256 sellerPre = token.balanceOf(seller);
        uint256 challengerPre = token.balanceOf(bidder3);

        // Harm suppression on the ERC-20 rail: the reject pays the seller and records no harm even
        // with a nonzero provenHarm; pin the selector at zero calls.
        _mockRecordClaim();
        vm.expectCall(address(operatorBond), abi.encodeWithSelector(IOperatorBond.recordClaim.selector), 0);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.BidIntegrityDisputeRejected(LOT_ID, 2, false);

        vm.prank(arbiter);
        a.resolveBidIntegrityDispute(LOT_ID, 2, false, uint128(1e6)); // nonzero harm, still records nothing

        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "ERC-20 reject clears the gate");
        assertEq(token.balanceOf(seller), sellerPre + INTEGRITY_BOND_AMT, "ERC-20 reject pays the bond to seller");
        assertEq(token.balanceOf(bidder3), challengerPre, "ERC-20 rejected challenger recovers nothing");
    }

    function test_ClassBLifecycleERC20_TimeoutPaysSeller() public {
        SessionAuction a = _freshDeliveredLot(address(token), seller);
        _openClassBOn(a, address(token), LOT_ID, 2, bidder3);

        uint256 sellerPre = token.balanceOf(seller);
        uint256 challengerPre = token.balanceOf(bidder3);

        // Harm suppression on the ERC-20 rail: the timeout resolves against the silent challenger
        // (bond to seller) and records no harm; pin the selector at zero calls.
        _mockRecordClaim();
        vm.expectCall(address(operatorBond), abi.encodeWithSelector(IOperatorBond.recordClaim.selector), 0);

        vm.warp(block.timestamp + INTEGRITY_TIMEOUT_SEC);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.BidIntegrityDisputeRejected(LOT_ID, 2, true); // byTimeout == true

        vm.prank(bidder1);
        a.timeoutBidIntegrityDispute(LOT_ID, 2);

        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "ERC-20 timeout clears the gate");
        assertEq(token.balanceOf(seller), sellerPre + INTEGRITY_BOND_AMT, "ERC-20 timeout pays the bond to seller");
        assertEq(token.balanceOf(bidder3), challengerPre, "ERC-20 silent challenger forfeits on timeout");
    }

    // ERC-20 rail + hostile token (transfer returns false, never reverts): on a reject the bond push
    // to the seller fails via trySafeTransfer -> false, so _pay parks it to _pendingWithdrawals
    // (WithdrawalCredited) and the resolve still clears the gate.
    function test_ClassBRejectHostileTokenParksBond() public {
        F_FalseReturningERC20 badToken = new F_FalseReturningERC20();
        // Fund the parties on the hostile token (deposit 10e6/bidder, bond INTEGRITY_BOND_AMT; mint
        // above both).
        badToken.mint(bidder1, 1e18);
        badToken.mint(bidder2, 1e18);
        badToken.mint(bidder3, uint256(INTEGRITY_BOND_AMT) + 1e18);

        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        vm.prank(address(hammer));
        a.initialize(_defaultInitConfig(address(badToken)));
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RAIL_RESERVE, uint64(block.timestamp + 1 days));

        _depositAndBidBad(a, badToken, bidder1, 0, RAIL_OVER_AMOUNT, RAIL_OVER_MAXBID, OVER_SALT, keccak256("BAD_Q1"));
        _depositAndBidBad(a, badToken, bidder2, RAIL_OVER_AMOUNT, RAIL_WIN_AMOUNT, RAIL_WIN_MAXBID, WINNER_SALT, keccak256("BAD_Q2"));

        vm.warp(block.timestamp + 1 days + 1);
        a.hammer(LOT_ID);
        // This hostile-token lot is built inline (not via _buildDeliveredLot), so reveal here too.
        _revealWinner(a, LOT_ID, RAIL_WIN_MAXBID, WINNER_SALT);
        vm.warp(block.timestamp + AC_CHALLENGE_SEC);
        a.finalizeWinner(LOT_ID);
        vm.prank(seller);
        a.markDelivered(LOT_ID, keccak256("bad-delivery"), "ipfs://bad");

        // Open the Class B bond (transferFrom still succeeds; only the push leg fails).
        vm.prank(bidder3);
        badToken.approve(address(a), INTEGRITY_BOND_AMT);
        vm.prank(bidder3);
        a.challengeAttestation(LOT_ID, 2, hex"deadbeef");

        // Reject: the seller push returns false, so the bond is parked, the resolve does NOT revert.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(seller, INTEGRITY_BOND_AMT);

        vm.prank(arbiter);
        a.resolveBidIntegrityDispute(LOT_ID, 2, false, 0);

        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "hostile-token reject still clears the gate");
        assertEq(a.pendingWithdrawal(seller), INTEGRITY_BOND_AMT, "hostile-token bond parked to pending");
    }

    // Reentrancy entry. All four integrity entrypoints are nonReentrant, and the bonded paths _pay a
    // potentially hostile recipient. Drive a reject that pays a seller whose receive() re-enters
    // resolveBidIntegrityDispute. resolveBidIntegrityDispute is `onlyArbiter nonReentrant` and
    // Solidity runs modifiers left-to-right, so onlyArbiter fires before the transient guard: the
    // non-arbiter re-entry reverts Unauthorized, one gate earlier than ReentrancyGuardReentrantCall.
    // (The guard itself is proven on the no-access-modifier entrypoints by the timeout /
    // cross-function tests.) The outer resolve still clears the gate with no double-pay.
    function test_RevertWhen_ResolveIntegrityReentered() public {
        // Clone first so the reentrant receiver can bind its address before openLot stores it as seller.
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        F_ReentrantReceiver hostile = new F_ReentrantReceiver(ISessionAuction(address(a)), LOT_ID, 2, 0);
        _buildDeliveredLot(a, address(0), address(hostile));
        _openClassBOn(a, address(0), LOT_ID, 2, bidder3);

        uint256 clonePre = address(a).balance; // holds exactly the one Class B bond pre-resolve

        vm.prank(arbiter);
        a.resolveBidIntegrityDispute(LOT_ID, 2, false, 0); // reject -> pays the hostile seller -> re-entry

        // The nested re-entry was attempted and rejected. bytes4 has no assertEq overload, so compare as
        // bytes32. The captured selector is Unauthorized (onlyArbiter reverts the non-arbiter re-entry
        // before the guard is reached), not ReentrancyGuardReentrantCall.
        assertTrue(hostile.reentered(), "the hostile seller did not attempt re-entry");
        assertEq(
            bytes32(hostile.caughtSelector()),
            bytes32(ISessionAuction.Unauthorized.selector),
            "non-arbiter re-entry was not rejected at onlyArbiter (which runs before the reentrancy guard)"
        );
        // No strand and no double-pay: the outer resolution still cleared the gate, and exactly one bond
        // left the clone (the single seller payout), so the blocked re-entry did not drive a second payout.
        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "reentered resolve must still clear the gate");
        assertEq(clonePre - address(a).balance, INTEGRITY_BOND_AMT, "exactly one bond left the clone (no double-pay on re-entry)");
    }

    // Same guard on the PERMISSIONLESS timeout path (also nonReentrant, also _pays the seller).
    function test_RevertWhen_TimeoutIntegrityReentered() public {
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        F_ReentrantReceiver hostile = new F_ReentrantReceiver(ISessionAuction(address(a)), LOT_ID, 2, 1);
        _buildDeliveredLot(a, address(0), address(hostile));
        _openClassBOn(a, address(0), LOT_ID, 2, bidder3);

        vm.warp(block.timestamp + INTEGRITY_TIMEOUT_SEC);
        vm.prank(bidder1);
        a.timeoutBidIntegrityDispute(LOT_ID, 2); // pays the hostile seller -> re-entry into timeout

        assertTrue(hostile.reentered(), "the hostile seller did not attempt re-entry on timeout");
        assertEq(
            bytes32(hostile.caughtSelector()),
            bytes32(ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector),
            "nested timeout re-entry was not blocked by the nonReentrant guard"
        );
        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "reentered timeout must still clear the gate");
    }

    // Cross-function reentry. The four integrity entrypoints share one transient guard, so a re-entry
    // from a bonded payout into a different nonReentrant entrypoint must also be blocked. Drive a
    // reject that pays a hostile seller whose receive() re-enters challengeAttestation on the other
    // seq; the shared guard rejects it with ReentrancyGuardReentrantCall (the modifier runs before the
    // native-rail WrongBond check, so a value-0 cross-call trips the guard first). reentered() and a
    // non-zero guard selector together prove the guard fired rather than the nested call quietly
    // running out of gas.
    function test_RevertWhen_CrossFunctionReenterChallengeAttestation() public {
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        // mode 2 re-enters challengeAttestation on the loser seq 1 (a distinct not-yet-open dispute). The
        // nested call carries value 0, so the proof is the captured selector: it must be the guard error
        // (modifier runs first), not WrongBond (the value-0 bond gate a guard-absent SUT would hit) and
        // not 0 (a successful open). The assertEq below distinguishes all three.
        F_ReentrantReceiver hostile = new F_ReentrantReceiver(ISessionAuction(address(a)), LOT_ID, 1, 2);
        _buildDeliveredLot(a, address(0), address(hostile));
        _openClassBOn(a, address(0), LOT_ID, 2, bidder3); // the outer dispute is on the winner seq 2

        vm.prank(arbiter);
        a.resolveBidIntegrityDispute(LOT_ID, 2, false, 0); // reject -> pays hostile seller -> cross-reenter

        assertTrue(hostile.reentered(), "hostile seller did not attempt the cross-function re-entry");
        assertEq(
            bytes32(hostile.caughtSelector()),
            bytes32(ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector),
            "cross-function re-entry into challengeAttestation was not blocked by the shared transient guard"
        );
        // The blocked cross-reentry did NOT open a second dispute (the guard reverted it whole): the
        // outer reject cleared seq 2 and seq 1 never opened, so the counter is 0, not 1.
        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "blocked cross-reentry must not open a second dispute");
    }

    // Uphold-branch reentry (_pay to challenger). The uphold branch of resolveBidIntegrityDispute
    // refunds the Class B bond via _pay to the challenger, a different recipient than the
    // reject/timeout seller, so the seller-branch reentrancy tests do not cover it. Here the hostile
    // receiver is the challenger: the uphold's bond-refund _pay triggers re-entry. mode 0 re-enters
    // resolveBidIntegrityDispute (the same function), so as in the reject test onlyArbiter reverts the
    // non-arbiter re-entry before the guard is reached.
    function test_RevertWhen_ResolveUpheldChallengerReenters() public {
        // Fresh native clone with a benign seller (the CHALLENGER is the reentry surface here). Clone
        // first so the hostile receiver can bind the clone address at construction.
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        F_ReentrantReceiver hostile = new F_ReentrantReceiver(ISessionAuction(address(a)), LOT_ID, 2, 0);
        _buildDeliveredLot(a, address(0), seller);

        // The hostile contract files the Class B dispute (so it is the bond refund recipient). It needs
        // ETH to post the bond; since it is sending, its receive() fires only on the uphold refund.
        vm.deal(address(hostile), INTEGRITY_BOND_AMT);
        _openClassBOn(a, address(0), LOT_ID, 2, address(hostile));
        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 1, "hostile challenger opened the Class B dispute");

        // Mock the harm write so the uphold reaches the bond-refund _pay (the reentry surface) instead of
        // the real recordClaim ledger write (a different concern, pinned elsewhere).
        _mockRecordClaim();

        vm.prank(arbiter);
        a.resolveBidIntegrityDispute(LOT_ID, 2, true, 1 ether); // UPHOLD -> _pay bond refund to hostile challenger -> re-entry

        // The nested re-entry from the bond-refund _pay was attempted and rejected. The captured selector
        // is Unauthorized: onlyArbiter reverts the non-arbiter challenger re-entering the same function
        // before the transient guard is reached.
        assertTrue(hostile.reentered(), "the hostile challenger did not attempt re-entry on the uphold refund");
        assertEq(
            bytes32(hostile.caughtSelector()),
            bytes32(ISessionAuction.Unauthorized.selector),
            "non-arbiter re-entry was not rejected at onlyArbiter (which runs before the reentrancy guard)"
        );
        // No strand: the outer uphold still cleared the gate. The receiver's receive() captures the
        // nested selector and returns (does not revert), so the bond-refund push succeeds; only the
        // nested re-entry is rejected by onlyArbiter.
        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "reentered uphold must still clear the gate");
    }

    // Uphold issues the real external bond claim. Every other uphold test mocks recordClaim, so a SUT
    // that dropped the harm write entirely would still satisfy vm.expectCall and pass. This test
    // upholds without the mock against the real AgentBond (recordClaim is a live onlyAuction ledger
    // write emitting ClaimRecorded; HammerBase registers the base `auction` as a clone so the
    // onlyAuction gate admits it). Assert the real ClaimRecorded event fires from operatorBond with
    // the exact (sessionId, victim, provenHarm), so a silently-skipped recordClaim fails both
    // expectCall and the event assertion.
    function test_ResolveUpheldIssuesRealBondClaim() public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 2, bidder3);

        uint128 provenHarm = 1 ether;
        uint256 challengerPre = bidder3.balance; // bond was debited at open; the uphold refunds it
        uint256 operatorBondPre = operatorBond.bondOf(SESSION_ID); // no operator staked here, so 0

        // No _mockRecordClaim(): the uphold issues the call into the live bond. The real recordClaim
        // records harm for the seq-2 victim (bidder2) and emits ClaimRecorded; with no prior recorded
        // harm totalClaims == provenHarm. The event from operatorBond (not the auction) proves the
        // cross-contract call landed in the bond.
        vm.expectCall(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder2, provenHarm))
        );
        vm.expectEmit(true, true, true, true, address(operatorBond));
        emit AgentBond.ClaimRecorded(SESSION_ID, bidder2, provenHarm, uint256(provenHarm));
        // The auction-side uphold event still fires with the same victim/harm.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityClaimUpheld(LOT_ID, 2, bidder2, provenHarm);

        vm.prank(arbiter);
        auction.resolveBidIntegrityDispute(LOT_ID, 2, true, provenHarm);

        // The resolve completed against the real bond: gate cleared, challenger bond refunded, bond pool
        // unchanged (recordClaim writes the harm ledger, not the stake pool; no operator deposited here).
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "real-bond uphold clears the gate");
        assertEq(bidder3.balance, challengerPre + INTEGRITY_BOND_AMT, "real-bond uphold refunds the challenger bond");
        assertEq(operatorBond.bondOf(SESSION_ID), operatorBondPre, "recordClaim writes the ledger, not the stake pool");
    }

    // A Class B uphold records the arbiter-supplied provenHarm. On an over-ceiling seq the on-chain
    // truth is harm == amount - maxBid (the Class A formula). Opens a Class B on the over-ceiling
    // loser seq 1 and upholds with provenHarm == that quantity, asserting recordClaim carries it with
    // victim == the seq principal. The companion test below drives an inflated arbiter value.
    function test_ResolveClassBUpheldOverCeilingRecordsComputedHarm() public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 1, bidder3); // Class B on the over-ceiling LOSER seq 1 (principal bidder1)
        _mockRecordClaim();

        uint128 computedHarm = OVER_AMOUNT - OVER_MAXBID; // the on-chain truth for seq 1

        // The recorded harm equals the on-chain amount - maxBid, credited to the seq-1 principal bidder1.
        vm.expectCall(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder1, computedHarm))
        );
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityClaimUpheld(LOT_ID, 1, bidder1, computedHarm);

        vm.prank(arbiter);
        auction.resolveBidIntegrityDispute(LOT_ID, 1, true, computedHarm);

        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "Class B uphold on the loser seq clears the gate");
    }

    // Companion: an inflated arbiter harm on the SAME over-ceiling seq. Class B records the supplied
    // provenHarm verbatim, unlike Class A which is computed from state. Asserts the inflated value
    // reaches both the event and recordClaim, catching a SUT that clamps it to amount - maxBid or
    // drops the write.
    function test_ResolveClassBUpheldArbiterHarmPassesThrough() public {
        _bootstrapHammeredLot();
        _openClassB(LOT_ID, 1, bidder3);
        _mockRecordClaim();

        // Deliberately INCONSISTENT with the on-chain amount-maxBid (which is OVER_AMOUNT - OVER_MAXBID).
        uint128 inflatedHarm = OVER_AMOUNT * 100;

        vm.expectCall(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder1, inflatedHarm))
        );
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityClaimUpheld(LOT_ID, 1, bidder1, inflatedHarm);

        vm.prank(arbiter);
        auction.resolveBidIntegrityDispute(LOT_ID, 1, true, inflatedHarm);

        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "uphold with arbiter-supplied harm clears the gate");
    }

    // A winner that landed over its committed ceiling. challengeOverCeiling on lot.winnerSeq must (a)
    // record harm with victim == the winner, (b) leave the gate at 0, and (c) not freeze the seller
    // _release (the buyer confirmReceipt still settles): the remedy is the slash pool, not an escrow
    // freeze.
    function test_ChallengeOverCeilingOnWinningSeqRecordsHarmNoFreeze() public {
        // A lot whose seq-2 WINNER landed amount > its committed maxBid (loser seq 1 stays low so seq 2
        // wins). The winner's amount exceeds WINOVER_MAXBID, so the commitment opens cleanly and amount >
        // maxBid holds.
        uint256 lotId = 7;
        _bootstrapWinnerOverCeilingLot(lotId);

        uint64 winnerSeq = auction.getLot(lotId).winnerSeq; // the over-ceiling WINNING seq
        uint128 expectedHarm = WINOVER_AMOUNT - WINOVER_MAXBID; // computed from on-chain state

        // Drive the winner to the release point (finalized + delivered) to prove the seller payout is
        // not frozen by a Class A on the winner.
        vm.warp(block.timestamp + AC_CHALLENGE_SEC);
        auction.finalizeWinner(lotId);
        vm.prank(seller);
        auction.markDelivered(lotId, keccak256("winover-delivery"), "ipfs://winover");

        _mockRecordClaim();
        // (a) harm recorded with victim == the WINNER (bidder2), harm == amount - maxBid.
        vm.expectCall(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder2, expectedHarm))
        );
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityDisputeOpened(lotId, winnerSeq, bidder2, 0, 0); // Class A: class 0, bond 0
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityClaimUpheld(lotId, winnerSeq, bidder2, expectedHarm);

        // Conservation (worst case): the disputed seq is the live winner escrow, so a SUT that shaved
        // escrowAmount on the self-proving call (leaving enough to release) would pass the
        // confirmReceipt below but break the no-escrow-touch rule. Snapshot the clone balance and
        // winner escrow across the challengeOverCeiling call (harm is recorded into the external bond
        // ledger, not by moving money).
        uint256 clonePreA = address(auction).balance;
        uint128 escrowPreA = auction.getLot(lotId).escrowAmount;

        vm.prank(bidder2); // the WINNER opens its own over-ceiling proof
        auction.challengeOverCeiling(lotId, winnerSeq, WINOVER_MAXBID, WINNER_SALT);

        // (b) the gate stays clean even though the disputed seq IS the winner.
        assertEq(auction.getLot(lotId).bidIntegrityOpen, 0, "Class A on the winner must not set the gate");
        assertFalse(auction.bidIntegrityDisputeOpen(lotId), "Class A on the winner never opens the release gate");

        // Conservation: the self-proving call moved no clone money and did not touch the winner escrow,
        // so the later release is funded by the intact escrow, not a shaved remainder.
        assertEq(address(auction).balance, clonePreA, "Class A on the winner must move no clone funds");
        assertEq(auction.getLot(lotId).escrowAmount, escrowPreA, "Class A must not touch the live winner escrow");

        // (c) the seller _release STILL proceeds: the winner confirms receipt and the lot settles.
        vm.prank(bidder2);
        auction.confirmReceipt(lotId, keccak256("winover-photo"), "ipfs://winover-photo");
        Lot memory afterRelease = auction.getLot(lotId);
        assertEq(uint8(afterRelease.phase), uint8(LotPhase.Settled), "Class A on the winner must not block release");
        assertEq(uint8(afterRelease.deliveryState), uint8(DeliveryState.Released), "released past a winner-seq Class A");
    }

    // Class A is self-proving and writes no IntegrityDispute, so nothing structurally rate-limits
    // repeated calls on the same seq; recording harm on every call would inflate the victim's
    // pro-rata slash share. Proves Class-A-then-Class-A records harm at most once (selector count 1).
    // A second call that reverts (e.g. an AlreadyDisputed-style guard) is also acceptable; either way
    // harm is not recorded twice.
    function test_ChallengeOverCeilingTwiceRecordsHarmOnce() public {
        _bootstrapHammeredLot();
        _mockRecordClaim();

        uint128 expectedHarm = OVER_AMOUNT - OVER_MAXBID;

        // The Class A record for seq 1 happens once with the right args and the selector fires once total,
        // so a second Class A that re-recorded would push the total to 2 and fail.
        vm.expectCall(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder1, expectedHarm)),
            1
        );
        vm.expectCall(address(operatorBond), abi.encodeWithSelector(IOperatorBond.recordClaim.selector), 1);

        // First Class A on seq 1: records harm once.
        vm.prank(bidder1);
        auction.challengeOverCeiling(LOT_ID, 1, OVER_MAXBID, OVER_SALT);

        // Second Class A on the same seq 1: must not record harm again. Either it is accepted (the
        // count-1 expectCall catches a double-record) or it reverts (also satisfies "recorded once").
        // No specific revert selector is asserted: the repeat may pass or revert, so long as harm is
        // not recorded twice.
        vm.prank(bidder1);
        try auction.challengeOverCeiling(LOT_ID, 1, OVER_MAXBID, OVER_SALT) {
            // accepted-again: the count-1 expectCall catches a double-record.
        } catch {
            // rejected-repeat: also acceptable.
        }
    }

    // Class A is always-available because the remedy is the slash pool, decoupled from _release: a
    // principal can prove over-ceiling even after the seller was paid. Drive the lot to Settled, then
    // a Class A on the over-ceiling loser seq must still record harm.
    function test_ChallengeOverCeilingAfterSettled() public {
        _bootstrapHammeredLot();

        // Settle the lot: finalize, deliver, confirm -> Released/Settled.
        vm.warp(block.timestamp + AC_CHALLENGE_SEC);
        auction.finalizeWinner(LOT_ID);
        vm.prank(seller);
        auction.markDelivered(LOT_ID, keccak256("settle-delivery"), "ipfs://settle");
        vm.prank(bidder2);
        auction.confirmReceipt(LOT_ID, keccak256("settle-photo"), "ipfs://settle-photo");
        assertEq(uint8(auction.getLot(LOT_ID).phase), uint8(LotPhase.Settled), "lot is Settled before the Class A");

        // Class A on the over-ceiling loser seq 1 still records harm post-Settled (victim == seq-1
        // principal bidder1, harm == amount - maxBid).
        _mockRecordClaim();
        uint128 expectedHarm = OVER_AMOUNT - OVER_MAXBID;
        vm.expectCall(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder1, expectedHarm))
        );
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityClaimUpheld(LOT_ID, 1, bidder1, expectedHarm);

        vm.prank(bidder1);
        auction.challengeOverCeiling(LOT_ID, 1, OVER_MAXBID, OVER_SALT);

        // Still no gate: Class A never touches it, even post-Settled.
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "Class A post-Settled must not set the gate");
    }

    // The over-ceiling proof is tied to a placed bid at any seq, not the lot phase. A bid placed on
    // an Open lot (before hammer) is the lower-phase case: the over-ceiling proof on that seq must
    // still record harm, catching a SUT that wrongly gated Class A to post-hammer phases.
    function test_ChallengeOverCeilingOnOpenLotBeforeHammer() public {
        uint256 lotId = 8;
        _init(address(0));
        vm.prank(address(hammer));
        auction.openLot(lotId, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));

        // A single over-ceiling bid on the still-OPEN lot (no hammer). seq 1, principal bidder1.
        _depositAndBid(lotId, bidder1, 0, 0, OVER_AMOUNT, OVER_MAXBID, OVER_SALT, keccak256(abi.encode("OPEN_Q1", lotId)));
        assertEq(uint8(auction.getLot(lotId).phase), uint8(LotPhase.Open), "lot is still Open (not hammered)");

        _mockRecordClaim();
        uint128 expectedHarm = OVER_AMOUNT - OVER_MAXBID;
        vm.expectCall(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder1, expectedHarm))
        );
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.BidIntegrityClaimUpheld(lotId, 1, bidder1, expectedHarm);

        vm.prank(bidder1);
        auction.challengeOverCeiling(lotId, 1, OVER_MAXBID, OVER_SALT);

        assertEq(auction.getLot(lotId).bidIntegrityOpen, 0, "Class A on an Open lot must not set the gate");
    }

    // A NoSale lot carries no challengeable bid, so a Class A over-ceiling proof reverts NotPrincipal
    // (empty slot). "Placed over-ceiling bid" and "NoSale" are mutually exclusive: placeBid enforces
    // amount >= reservePrice for the first bid (BidTooLow), so a sub-reserve bid reverts at bid time
    // and records no top; the hammer NoSale branch is reached only via the no-bid disjunct
    // (highBidder == address(0)). The over-ceiling proof targets the stored bid for the seq, the zero
    // principal on a bid-less NoSale lot, so it reverts NotPrincipal.
    function test_ChallengeOverCeilingOnNoSaleLot() public {
        uint256 lotId = 9;
        _init(address(0));
        // Reserve well ABOVE any bid so the lot cannot sell. NOSALE_RESERVE > NOSALE_AMOUNT.
        vm.prank(address(hammer));
        auction.openLot(lotId, seller, NOSALE_RESERVE, uint64(block.timestamp + 1 days));

        // Drive to a genuine NoSale: the sub-reserve bid attempt is rejected at the placeBid reserve floor
        // (BidTooLow), recording no top, so the lot is bid-less and hammers to NoSale. Fund the deposit
        // first so the revert isolates to the reserve floor, not an escrow shortfall. NOSALE_AMOUNT is the
        // sub-reserve bid (also over its own ceiling, but it never lands).
        vm.prank(bidder1);
        auction.depositCeiling{value: 10 ether}(lotId, 10 ether);
        Ceiling memory c = _ceiling(lotId, bidder1, NOSALE_MAXBID, OVER_SALT);
        AttestationQuote memory q = _quote(c, lotId, NOSALE_AMOUNT, 0, 0, keccak256(abi.encode("NOSALE_Q1", lotId)));
        bytes memory sig = _signCeiling(address(auction), c, _signerKeyFor(bidder1));
        _mockPaddle(bidder1, _paddleFor(bidder1)); // pass KYC so the revert is the reserve floor, not Unauthorized
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.BidTooLow.selector);
        auction.placeBid(c, lotId, bidder1, 0, NOSALE_AMOUNT, sig, _baseOperatorKeyId(), q);

        vm.warp(block.timestamp + 1 days + 1);
        auction.hammer(lotId); // no qualifying bid -> NoSale (the no-bid disjunct)
        Lot memory noSale = auction.getLot(lotId);
        assertEq(uint8(noSale.phase), uint8(LotPhase.NoSale), "lot hammered to NoSale");
        assertEq(noSale.highBidder, address(0), "NoSale lot is bid-less (no top recorded below reserve)");

        // No placed bid at any seq, so the over-ceiling proof targets an empty slot and reverts
        // NotPrincipal. Probe seq 1 (the seq the sub-reserve attempt would have taken); it was never
        // recorded.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.NotPrincipal.selector);
        auction.challengeOverCeiling(lotId, 1, NOSALE_MAXBID, OVER_SALT);

        // The failed Class A left the gate untouched (it never reached the harm-record path).
        assertEq(auction.getLot(lotId).bidIntegrityOpen, 0, "Class A on a NoSale lot must not set the gate");
    }

    // The Class B analogue of test_RevertWhen_ChallengeOverCeilingUnknownSeq: a bonded challenge on a
    // never-placed seq (stored bid principal == address(0)) is rejected before any bond is pulled, so
    // a griefer cannot strand a bond against a phantom seq. The empty-seq revert is NotPrincipal (the
    // same zero-principal branch Class A uses); gate and clone balance are asserted unchanged.
    function test_RevertWhen_ChallengeAttestationUnknownSeq() public {
        _bootstrapHammeredLot();

        uint256 clonePre = address(auction).balance;
        uint256 challengerPre = bidder3.balance;

        // seq 999 was never placed; its stored principal is address(0).
        vm.prank(bidder3);
        vm.expectRevert(ISessionAuction.NotPrincipal.selector);
        auction.challengeAttestation{value: INTEGRITY_BOND_AMT}(LOT_ID, 999, hex"deadbeef");

        // Fails closed: no dispute opened and (because the call reverted whole) no bond moved.
        assertEq(auction.getLot(LOT_ID).bidIntegrityOpen, 0, "unknown-seq Class B must not open a dispute");
        assertEq(address(auction).balance, clonePre, "unknown-seq Class B must not pull a bond into the clone");
        assertEq(bidder3.balance, challengerPre, "unknown-seq Class B must not debit the challenger");
    }

    // reject pays lot.seller, not the disputed seq's bidder. A Class B can attach to a losing seq, and
    // resolving it pays the bond to the seller regardless of which seq the evidence named. Here the
    // dispute is on the loser seq 1 (bidder1) and the lot has a distinct seller, so a SUT mis-deriving
    // the payout recipient from the disputed seq's bidder is caught: the bond flows to lot.seller,
    // never bidder1.
    function test_ResolveLoserSeqRejectPaysLotSeller() public {
        // Fresh native clone with the canonical `seller` actor (distinct from loser-seq bidder1).
        SessionAuction a = _freshDeliveredLot(address(0), seller);
        _openClassBOn(a, address(0), LOT_ID, 1, bidder3); // Class B on the LOSER seq 1 (principal bidder1)

        uint256 sellerPre = seller.balance;
        uint256 loserBidderPre = bidder1.balance; // the disputed seq's principal: must NOT receive the bond

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.BidIntegrityDisputeRejected(LOT_ID, 1, false);

        vm.prank(arbiter);
        a.resolveBidIntegrityDispute(LOT_ID, 1, false, 0);

        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "loser-seq reject clears the gate");
        // The payout recipient is the LOT seller, independent of the disputed seq.
        assertEq(seller.balance, sellerPre + INTEGRITY_BOND_AMT, "loser-seq reject pays the bond to lot.seller");
        assertEq(bidder1.balance, loserBidderPre, "loser-seq reject must NOT pay the disputed seq's bidder");
    }

    // The timeout anchor is IntegrityDispute.openedAt, which has no getter, so it is pinned
    // behaviorally: open the dispute at a block.timestamp strictly after markDelivered (warp between
    // them), then measure the boundary from the open instant. If the SUT anchored on deliveredAt (or
    // hammeredAt) the window would be partly elapsed at open and these two boundary assertions would
    // not both hold: WindowOpen at openInstant + TIMEOUT - 1, fires at openInstant + TIMEOUT.
    function test_TimeoutAnchorIsOpenTimeNotDelivery() public {
        // Build a delivered lot WITHOUT opening the dispute yet, so we control the open instant.
        SessionAuction a = _freshDeliveredLot(address(0), seller);

        // Advance time after delivery but before opening the dispute. If the SUT anchored on deliveredAt,
        // this gap would be counted against the timeout window.
        uint256 gap = INTEGRITY_TIMEOUT_SEC / 2 + 1234; // a non-trivial separation from deliveredAt
        vm.warp(block.timestamp + gap);

        // Open the Class B dispute now: openedAt must equal this block.timestamp.
        _openClassBOn(a, address(0), LOT_ID, 2, bidder3);
        uint256 openInstant = block.timestamp;

        // Just before the window closes (measured from the OPEN instant): still WindowOpen.
        vm.warp(openInstant + INTEGRITY_TIMEOUT_SEC - 1);
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WindowOpen.selector);
        a.timeoutBidIntegrityDispute(LOT_ID, 2);

        // Exactly at the open instant + timeout: the backstop fires. Had the SUT anchored on deliveredAt
        // the window would have elapsed `gap` seconds earlier, contradicting the WindowOpen assertion
        // above; the pair both hold only if the anchor is openedAt.
        vm.warp(openInstant + INTEGRITY_TIMEOUT_SEC);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.BidIntegrityDisputeRejected(LOT_ID, 2, true); // byTimeout == true
        vm.prank(bidder1);
        a.timeoutBidIntegrityDispute(LOT_ID, 2);

        assertEq(a.getLot(LOT_ID).bidIntegrityOpen, 0, "open-anchored timeout fired and cleared the gate");
    }

    // A second anchor pin independent of deliveredAt: the window must still be open immediately after
    // the open instant even though the lot was hammered/delivered well earlier. A SUT anchoring on
    // hammeredAt would have a window already elapsed by open time (the AC window + delivery setup
    // advance time), so a timeout one second after open would wrongly succeed; here it must revert
    // WindowOpen.
    function test_TimeoutWindowOpenImmediatelyAfterOpen() public {
        SessionAuction a = _freshDeliveredLot(address(0), seller);

        // Open the dispute; the window is anchored to NOW (openedAt), so one second later it is still open.
        _openClassBOn(a, address(0), LOT_ID, 2, bidder3);
        vm.warp(block.timestamp + 1);

        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WindowOpen.selector);
        a.timeoutBidIntegrityDispute(LOT_ID, 2);
    }

    // Winner-over-ceiling fixture. Bootstrap a lot whose winning seq (seq 2) landed amount > its
    // committed maxBid. Loser seq 1 is a low on-policy bid so seq 2 wins; the winner commits
    // WINOVER_MAXBID under WINNER_SALT and lands WINOVER_AMOUNT (> WINOVER_MAXBID), so the commitment
    // opens cleanly and amount > maxBid holds. RESERVE_PRICE <= WINOVER_AMOUNT so the lot sells.
    function _bootstrapWinnerOverCeilingLot(uint256 lotId) private {
        _init(address(0));
        vm.prank(address(hammer));
        auction.openLot(lotId, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));

        // seq 1: a low on-policy loser (amount < WINOVER_AMOUNT), committed below its own ceiling.
        _depositAndBid(lotId, bidder1, 0, 0, OVER_MAXBID, WINNER_MAXBID, OVER_SALT, keccak256(abi.encode("WOC1", lotId)));
        // seq 2: the winner lands over its committed ceiling. prevTop is bidder1's standing top
        // (OVER_MAXBID); WINOVER_AMOUNT clears the min increment.
        _depositAndBid(lotId, bidder2, OVER_MAXBID, 0, WINOVER_AMOUNT, WINOVER_MAXBID, WINNER_SALT, keccak256(abi.encode("WOC2", lotId)));

        vm.warp(block.timestamp + 1 days + 1);
        auction.hammer(lotId);
        // Reveal so the test's subsequent finalizeWinner clears the reveal gate; see _revealWinner.
        _revealWinner(auction, lotId, WINOVER_MAXBID, WINNER_SALT);
    }

    // Winner-over-ceiling and no-sale constants.
    // Winner that lands over its own ceiling: committed 2 ether, lands 4 ether (4 > 2 over-ceiling; 4 >
    // the seq-1 top of 1 ether and clears the 2% min increment; 4 >= RESERVE_PRICE so the lot sells).
    uint128 private constant WINOVER_MAXBID = 2 ether;
    uint128 private constant WINOVER_AMOUNT = 4 ether;

    // NoSale fixture: one bid over its own ceiling (2 > 1) but below a high reserve (5 ether) so the lot
    // hammers to NoSale while the over-ceiling bid record still exists at its seq.
    uint96  private constant NOSALE_RESERVE = 5 ether;
    uint128 private constant NOSALE_MAXBID  = 1 ether;
    uint128 private constant NOSALE_AMOUNT  = 2 ether;

    // One-wei-over boundary fixture (minimal positive harm): committed ceiling 1 ether, lands exactly
    // 1 ether + 1 wei, so bidAmount - maxBid == 1 (the smallest value for which the strict bidAmount >
    // maxBid check is TRUE). The landed amount >= RESERVE_PRICE so seq 1 is valid; a higher seq 2 wins.
    // Dedicated salt so its commitment opening is independent of the OVER/WINNER fixtures.
    uint128 private constant WONE_MAXBID = 1 ether;
    uint128 private constant WONE_AMOUNT = 1 ether + 1; // one wei over the committed ceiling
    bytes32 private constant WONE_SALT   = keccak256("F_DOMAIN_WONE_SALT_v1");

    // IntegrityDispute.bond is uint96, validated at config time. INTEGRITY_BOND_AMT (0.1 ether) fits
    // uint96; the boundary integrityBondAmt > type(uint96).max -> WrongBond is covered by the config
    // validation tests, not retested here.

    // Hostile-token helper. Deposit + bid for `principal` on the hostile-token clone `a` (transferFrom
    // succeeds; only the _pay push leg fails). Separate so the false-returning token type stays local.
    function _depositAndBidBad(
        SessionAuction a,
        F_FalseReturningERC20 t,
        address principal,
        uint128 prevTop,
        uint128 amount,
        uint128 maxBid,
        bytes32 salt,
        bytes32 quoteNonce
    ) private {
        vm.prank(principal);
        t.approve(address(a), 10e6);
        vm.prank(principal);
        a.depositCeiling(LOT_ID, 10e6);

        Ceiling memory c = _ceiling(LOT_ID, principal, maxBid, salt);
        AttestationQuote memory q = _quote(c, LOT_ID, amount, 0, prevTop, quoteNonce);
        bytes32 keyId = _baseOperatorKeyId();
        // Real ceiling sig over this clone's domain + KYC paddle; the hostile token only fails the _pay
        // push leg, not deposit/bid authz.
        bytes memory sig = _signCeiling(address(a), c, _signerKeyFor(principal));
        _mockPaddle(principal, _paddleFor(principal));

        vm.prank(principal);
        a.placeBid(c, LOT_ID, principal, 0, amount, sig, keyId, q);
    }
}
