// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Escrow and funds: deposit, commit-rebalance, lock, withdraw, failed-push.
//
// Every test drives the real clone-deploy + initialize flow (initialize sets _hammer so the
// onlyHammer openLot passes). The ERC-20 rail is genuinely token-denominated
// (paymentToken == address(token)), not a native instance masquerading as ERC-20. Bid fixtures
// attest under the operator (qx, qy) key _defaultInitConfig seeds and carry a real EIP-712 ceiling
// signature over the clone domain. Errors and events are bound to ISessionAuction.

import {HammerBase} from "./HammerBase.t.sol";

import {SessionAuction} from "../src/SessionAuction.sol";
import {ISessionAuction} from "../src/interfaces/ISessionAuction.sol";
import {IPaddleRegistry} from "../src/interfaces/IPaddleRegistry.sol";
import {MockERC20} from "./mocks/MockERC20.sol";
import {
    Ceiling,
    AttestationQuote,
    InitConfig,
    Lot,
    LotPhase,
    DeliveryState,
    CEILING_TYPEHASH
} from "../src/types/HammerTypes.sol";

import {ReentrancyGuardTransient} from "@openzeppelin/contracts/utils/ReentrancyGuardTransient.sol";
import {Clones} from "@openzeppelin/contracts/proxy/Clones.sol";
import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";
import {Nonces} from "@openzeppelin/contracts/utils/Nonces.sol";
import {IERC1271} from "@openzeppelin/contracts/interfaces/IERC1271.sol";
import {ECDSA} from "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";

contract EscrowFundsTest is HammerBase {
    uint256 private constant LOT_ID = 1;

    SessionAuction private auctionN; // native rail clone (paymentToken == address(0))
    SessionAuction private auctionT; // ERC-20 rail clone (paymentToken == address(token))

    // Token-denominated amounts (6 decimals, mirroring USDC).
    uint96  private constant RESERVE_TOKEN = 1_000e6;
    uint128 private constant CEILING_A     = 5_000e6;   // bidder1 ceiling/deposit (token rail)
    uint128 private constant CEILING_B     = 5_000e6;   // bidder2 ceiling/deposit (token rail)
    uint128 private constant BID_A         = 1_000e6;   // A's top bid (== reserve)
    uint128 private constant BID_B         = 1_500e6;   // B outbids A (>= A + 2% min increment)

    // Native-rail amounts.
    uint128 private constant N_CEILING_A = 5 ether;
    uint128 private constant N_BID_A     = 1 ether;     // == RESERVE_PRICE

    // bidder signing keys, bound to the addresses HammerBase.setUp produced via makeAddr.
    uint256 private bidder1Key;
    uint256 private bidder2Key;

    // EIP-712 domain pieces for a clone; the verifyingContract is the clone address.
    bytes32 private constant EIP712_TYPE_HASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 private constant HASHED_NAME = keccak256(bytes("Hammer"));
    bytes32 private constant HASHED_VERSION = keccak256(bytes("1"));

    function setUp() public override {
        super.setUp();

        // Recover the signing keys for the named bidder addresses so ceiling envelopes carry a real
        // ECDSA signature over the clone domain.
        (, bidder1Key) = makeAddrAndKey("bidder1");
        (, bidder2Key) = makeAddrAndKey("bidder2");

        // Fresh per-rail clones of the impl (the impl itself is locked by _disableInitializers).
        // Each test calls initialize on the clone it uses.
        auctionN = SessionAuction(Clones.clone(address(impl)));
        auctionT = SessionAuction(Clones.clone(address(impl)));
    }

    // Pre-state drivers.

    /// @dev Initialize `a` for `payToken` (native if address(0)) and open LOT_ID via the hammer.
    ///      _defaultInitConfig seeds the operator (qx, qy) pair the bid fixtures attest under and sets
    ///      _hammer == address(hammer) so openLot's onlyHammer gate passes.
    function _initAndOpen(SessionAuction a, address payToken, uint96 reserve, uint64 endsAt) private {
        InitConfig memory cfg = _defaultInitConfig(payToken);
        a.initialize(cfg);

        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, reserve, endsAt);
    }

    /// @dev Same as _initAndOpen but with an explicit seller (used to install a hostile receiver seller).
    function _initAndOpenWithSeller(
        SessionAuction a,
        address payToken,
        uint96 reserve,
        uint64 endsAt,
        address theSeller
    ) private {
        InitConfig memory cfg = _defaultInitConfig(payToken);
        a.initialize(cfg);

        vm.prank(address(hammer));
        a.openLot(LOT_ID, theSeller, reserve, endsAt);
    }

    /// @dev depositCeiling for `principal`. Native sends msg.value == amount; ERC-20 approves the
    ///      clone then sends msg.value == 0.
    function _deposit(SessionAuction a, address payToken, address principal, uint128 amount) private {
        if (payToken == address(0)) {
            vm.deal(principal, principal.balance + uint256(amount));
            vm.prank(principal);
            a.depositCeiling{value: amount}(LOT_ID, amount);
        } else {
            MockERC20(payToken).mint(principal, uint256(amount));
            vm.prank(principal);
            MockERC20(payToken).approve(address(a), amount);
            vm.prank(principal);
            a.depositCeiling(LOT_ID, amount);
        }
    }

    /// @dev Place one bid for `principal` carrying a real EIP-712 ceiling signature over the clone
    ///      domain and a structurally correct attestation quote. operatorKeyId is the seeded key.
    ///      ceilingCommit hides maxBid == `amount` under bytes32("salt") so the winner can later reveal.
    function _placeBid(
        SessionAuction a,
        address principal,
        uint256 signerKey,
        uint64 bidIndex,
        uint128 amount,
        uint128 observedPrevTop,
        bytes32 quoteNonce
    ) private {
        Ceiling memory c = Ceiling({
            principal: principal,
            sessionId: SESSION_ID,
            lotId: LOT_ID,
            ceilingCommit: keccak256(abi.encode(uint128(amount), bytes32("salt"))),
            strategy: 0,
            deadline: uint64(block.timestamp + 1 hours),
            maxBids: uint64(MAX_EXTENSIONS) + 8,
            nonceKey: uint192(uint256(keccak256(abi.encode(SESSION_ID, LOT_ID, principal))))
        });
        bytes memory sig = _signCeiling(address(a), c, signerKey);
        AttestationQuote memory q = _realQuote(c, LOT_ID, amount, bidIndex, observedPrevTop, quoteNonce);

        // placeBid gates on KYC: the PaddleRegistry stub returns paddleOf == 0, which would revert
        // Unauthorized(). A distinct nonzero paddle per principal keeps lot.paddleId on the real bidder.
        _mockPaddle(principal, _paddleFor(principal));

        // Caller is irrelevant: the principal is bound by the ceiling signature, not msg.sender.
        vm.prank(principal);
        a.placeBid(c, LOT_ID, principal, bidIndex, amount, sig, _operatorKeyId(), q);
    }

    /// @dev Drive `a` (native rail, fixed seller) to a Hammered lot with winner == bidder1 holding
    ///      escrowAmount == bid. Path: initialize -> openLot -> depositCeiling -> placeBid -> hammer.
    function _driveToHammered(SessionAuction a, address theSeller, uint128 deposit, uint128 bid) private {
        uint64 endsAt = uint64(block.timestamp + 1 days);
        _initAndOpenWithSeller(a, address(0), RESERVE_PRICE, endsAt, theSeller);
        _deposit(a, address(0), bidder1, deposit);
        _placeBid(a, bidder1, bidder1Key, 0, bid, 0, keccak256("qn-win"));

        vm.warp(endsAt);
        a.hammer(LOT_ID);
    }

    /// @dev Drive `a` (native rail) to DeliveryState.AwaitingDelivery carrying escrow == bid.
    function _driveToAwaiting(SessionAuction a, address theSeller, uint128 deposit, uint128 bid) private {
        _driveToHammered(a, theSeller, deposit, bid);

        // Read winnerSeq before vm.prank: an inline getLot argument would consume the prank, so reveal
        // would run unpranked and revert NotPrincipal.
        uint64 wseq = a.getLot(LOT_ID).winnerSeq;

        // Reveal the winning bid (satisfies the reveal gate), close the challenge window, finalize.
        vm.prank(bidder1);
        a.reveal(LOT_ID, wseq, bid, bytes32("salt"));

        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        a.finalizeWinner(LOT_ID);
    }

    /// @dev Drive `a` (native rail) to DeliveryState.Delivered (seller has marked delivered).
    function _driveToDelivered(SessionAuction a, address theSeller, uint128 deposit, uint128 bid) private {
        _driveToAwaiting(a, theSeller, deposit, bid);

        vm.prank(theSeller);
        a.markDelivered(LOT_ID, keccak256("proof"), "ipfs://proof");
    }

    /// @dev Drive `a` (native rail, fixed EOA seller) to AwaitingDelivery with `buyerContract` as the
    ///      winner: an ERC-1271 contract whose isValidSignature recovers to the bidder1 key. deposit ==
    ///      bid == N_BID_A, so the winner's free ends at 0. The bid envelope is signed with bidder1Key
    ///      and SignatureChecker routes the contract principal through the ERC-1271 branch.
    function _driveToAwaitingWithBuyer(SessionAuction a, address buyerContract) private {
        uint64 endsAt = uint64(block.timestamp + 1 days);
        _initAndOpenWithSeller(a, address(0), RESERVE_PRICE, endsAt, seller);

        // Fund the buyer contract's native deposit (deposit == bid, so free ends at 0 post-hammer).
        vm.deal(buyerContract, uint256(N_BID_A));
        vm.prank(buyerContract);
        a.depositCeiling{value: N_BID_A}(LOT_ID, N_BID_A);

        // Place the winning bid as the ERC-1271 buyer principal (signed with bidder1Key).
        _placeBid(a, buyerContract, bidder1Key, 0, N_BID_A, 0, keccak256("qn-buyer"));

        vm.warp(endsAt);
        a.hammer(LOT_ID);

        // Read winnerSeq before the prank (else the inline getLot argument consumes it).
        uint64 wseq = a.getLot(LOT_ID).winnerSeq;

        // Reveal as the buyer principal, close the challenge window, finalize into AwaitingDelivery.
        vm.prank(buyerContract);
        a.reveal(LOT_ID, wseq, N_BID_A, bytes32("salt"));

        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        a.finalizeWinner(LOT_ID);
    }

    // Pure and view helpers.

    function _operatorKeyId() private view returns (bytes32) {
        return _baseOperatorKeyId(); // the on-curve operator key _defaultInitConfig seeds
    }

    /// @dev Mock PaddleRegistry.paddleOf(principal) -> a nonzero KYC paddle so the placeBid KYC gate
    ///      passes; the stub returns 0 and would revert Unauthorized(). The exact value is irrelevant
    ///      here (no escrow path reads paddleId).
    function _mockPaddle(address principal, uint16 paddleId) private {
        vm.mockCall(
            address(paddles),
            abi.encodeWithSelector(IPaddleRegistry.paddleOf.selector, principal),
            abi.encode(paddleId)
        );
    }

    /// @dev A stable distinct nonzero paddle for `principal`. OR-ing 0x8000 sets the top bit, so the
    ///      result is always in [0x8000, 0xFFFF] and can never collapse to paddle 0 (unregistered).
    function _paddleFor(address principal) private pure returns (uint16) {
        return uint16(uint256(uint160(principal)) & 0x7FFF) | 0x8000;
    }

    /// @dev The keyed-nonce key the envelope binds for `principal` on LOT_ID. _placeBid sets c.nonceKey
    ///      to exactly this, so the on-chain _useCheckedNonce consumes under it.
    function _nonceKeyOf(address principal) private pure returns (uint192) {
        return uint192(uint256(keccak256(abi.encode(SESSION_ID, LOT_ID, principal))));
    }

    /// @dev The packed keyNonce NoncesKeyed reports in InvalidAccountNonce(owner, current) for a keyed
    ///      (nonzero-key) nonce: (uint256(key) << 64) | nonce. The bid path uses a nonzero key, so the
    ///      revert carries this packed value, not the bare nonce.
    function _packedKeyNonce(address principal, uint64 nonce) private pure returns (uint256) {
        return (uint256(_nonceKeyOf(principal)) << 64) | uint256(nonce);
    }

    function _domainSeparator(address clone) private view returns (bytes32) {
        return keccak256(abi.encode(EIP712_TYPE_HASH, HASHED_NAME, HASHED_VERSION, block.chainid, clone));
    }

    /// @dev Sign the Ceiling over the clone EIP-712 domain (matches the contract's _hashCeiling).
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

    /// @notice Token-balance conservation sum for the ERC-20 rail on `a`: winner escrow + dispute bond +
    ///         committed-behind-the-top (== lot.highBid while Open) + free(all) + pending(all). Equals
    ///         token.balanceOf(a) only before any _release / _refund leg fires, since a payout moves
    ///         tokens out of the contract. `who` must enumerate every actor that can hold a free or
    ///         pending balance, including the house fee recipient.
    function _erc20Buckets(SessionAuction a, address[4] memory who)
        private
        view
        returns (uint256 total)
    {
        Lot memory lot = a.getLot(LOT_ID);
        total = uint256(lot.escrowAmount);          // winner escrow (set at hammer)
        total += uint256(lot.disputeBond);          // dispute bond (separate pool, 0 here)

        // The standing top bid is committed (not in any free bucket) only while the lot is still Open.
        if (uint8(lot.phase) == uint8(LotPhase.Open)) {
            total += uint256(lot.highBid);
        }

        for (uint256 i = 0; i < who.length; i++) {
            total += a.withdrawableFree(LOT_ID, who[i]); // free bucket
            total += a.pendingWithdrawal(who[i]);        // failed-push credit bucket
        }
    }

    /// @notice Native-rail mirror of _erc20Buckets: the same bucket sum measured against
    ///         `address(a).balance`. The caller asserts buckets == balance only when every push
    ///         recipient is a bucket-tracked credit (failed-push or parked proceeds), or otherwise
    ///         snapshots a before/after delta when wei genuinely leaves to a non-tracked EOA. `who` must
    ///         enumerate every actor that can hold a free, committed, or pending balance.
    function _nativeBuckets(SessionAuction a, address[4] memory who)
        private
        view
        returns (uint256 total)
    {
        Lot memory lot = a.getLot(LOT_ID);
        total = uint256(lot.escrowAmount);          // winner escrow (set at hammer)
        total += uint256(lot.disputeBond);          // dispute bond (separate pool, 0 here)

        // The standing top bid is committed (not in any free bucket) only while the lot is still Open.
        if (uint8(lot.phase) == uint8(LotPhase.Open)) {
            total += uint256(lot.highBid);
        }

        for (uint256 i = 0; i < who.length; i++) {
            total += a.withdrawableFree(LOT_ID, who[i]); // free bucket
            total += a.pendingWithdrawal(who[i]);        // failed-push credit bucket
        }
    }

    /// @dev Initialize `a` (native rail, fixed seller) and fund two native bidders, so the native
    ///      commit-rebalance and fail-closed paths run on a genuinely native-denominated clone where the
    ///      pull is msg.value == amount, not safeTransferFrom.
    function _openTwoFundedNative(SessionAuction a, uint128 depA, uint128 depB) private {
        _initAndOpen(a, address(0), RESERVE_PRICE, uint64(block.timestamp + 1 days));
        _deposit(a, address(0), bidder1, depA);
        _deposit(a, address(0), bidder2, depB);
    }

    // _commitBid moves the new top free->committed and the prior top's entire committed->free, with no
    // external transfer; total escrow held is conserved.
    function test_CommitBidRebalancesNoTransfer() public {
        address[4] memory who = [bidder1, bidder2, seller, houseFeeRecipient];

        _initAndOpen(auctionT, address(token), RESERVE_TOKEN, uint64(block.timestamp + 1 days));
        _deposit(auctionT, address(token), bidder1, CEILING_A);
        _deposit(auctionT, address(token), bidder2, CEILING_B);

        // A opens the bidding: committed == BID_A, free == CEILING_A - BID_A. prevTop == address(0) on an
        // opening bid, so the released-from-prior-top amount is 0.
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.BidEscrowCommitted(LOT_ID, bidder1, BID_A, address(0), 0);
        _placeBid(auctionT, bidder1, bidder1Key, 0, BID_A, 0, keccak256("qn-A"));

        // Snapshot the full conserved bucket sum + the raw token balance BEFORE B outbids.
        uint256 balBefore = token.balanceOf(address(auctionT));
        uint256 bucketsBefore = _erc20Buckets(auctionT, who);
        uint256 aFreeBefore = auctionT.withdrawableFree(LOT_ID, bidder1);
        uint256 bFreeBefore = auctionT.withdrawableFree(LOT_ID, bidder2);

        // B outbids (observedPrevTop == A's standing BID_A). Events fire in order: BidPlaced,
        // TopBidChanged, BidEscrowCommitted. The released-from-prior-top amount is A's free after A's
        // committed returned (CEILING_A - BID_A + BID_A == CEILING_A).
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.BidPlaced(LOT_ID, bidder2, BID_B, 2);
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.TopBidChanged(LOT_ID, bidder2, BID_B);
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.BidEscrowCommitted(LOT_ID, bidder2, BID_B, bidder1, CEILING_A);

        _placeBid(auctionT, bidder2, bidder2Key, 0, BID_B, BID_A, keccak256("qn-B"));

        // 1. No external transfer: the contract token balance is unchanged by the rebalance.
        assertEq(token.balanceOf(address(auctionT)), balBefore, "C-01: contract balance moved");

        // 2. A fully refunded to withdrawable: A.committed -> A.free, so A.free == CEILING_A.
        assertEq(
            auctionT.withdrawableFree(LOT_ID, bidder1),
            aFreeBefore + BID_A,
            "C-01: A committed not released to free"
        );
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder1), CEILING_A, "C-01: A free != full deposit");

        // 3. B debited free by BID_B; B holds the only nonzero committed, so free == deposit - highBid.
        assertEq(
            auctionT.withdrawableFree(LOT_ID, bidder2),
            bFreeBefore - BID_B,
            "C-01: B free not debited by amount"
        );
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder2), CEILING_B - BID_B, "C-01: B free != deposit - highBid");

        // 4. Lot hot slot reflects B as the new top.
        Lot memory lot = auctionT.getLot(LOT_ID);
        assertEq(lot.highBidder, bidder2, "C-01: highBidder not B");
        assertEq(uint256(lot.highBid), BID_B, "C-01: highBid not B amount");

        // 5. Conservation: every bucket sums to the same total across the rebalance (pre-release).
        assertEq(_erc20Buckets(auctionT, who), bucketsBefore, "C-01: bucket sum changed");
        assertEq(_erc20Buckets(auctionT, who), balBefore, "C-01: buckets != contract balance");
    }

    // Commit-rebalance accounting on a genuinely native-denominated clone. The native pull
    // (msg.value == amount) differs from ERC-20 safeTransferFrom, so a native-specific regression in
    // _commitBid bucket math would be invisible on the ERC-20 test above.
    function test_CommitBidRebalancesNoTransferNative() public {
        address[4] memory who = [bidder1, bidder2, seller, houseFeeRecipient];

        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _openTwoFundedNative(a, N_CEILING_A, N_CEILING_A);

        // A opens: prevTop == address(0), so the released-from-prior-top amount is 0.
        uint128 nBidB = uint128(uint256(N_BID_A) * 2); // strictly higher, well over the 2% increment
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.BidEscrowCommitted(LOT_ID, bidder1, N_BID_A, address(0), 0);
        _placeBid(a, bidder1, bidder1Key, 0, N_BID_A, 0, keccak256("qn-AN"));

        // Snapshot the conserved bucket sum and raw balance before B outbids.
        uint256 balBefore = address(a).balance;
        uint256 bucketsBefore = _nativeBuckets(a, who);
        uint256 aFreeBefore = a.withdrawableFree(LOT_ID, bidder1);
        uint256 bFreeBefore = a.withdrawableFree(LOT_ID, bidder2);
        assertEq(bucketsBefore, balBefore, "C-01N: buckets != contract balance pre-outbid");

        // B outbids: the released-from-prior-top amount is A's free after A's committed returns
        // (N_CEILING_A).
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.BidPlaced(LOT_ID, bidder2, nBidB, 2);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.TopBidChanged(LOT_ID, bidder2, nBidB);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.BidEscrowCommitted(LOT_ID, bidder2, nBidB, bidder1, N_CEILING_A);
        _placeBid(a, bidder2, bidder2Key, 0, nBidB, uint128(N_BID_A), keccak256("qn-BN"));

        // No native transfer on the rebalance; A fully released to free; B debited by amount.
        assertEq(address(a).balance, balBefore, "C-01N: contract balance moved on rebalance");
        assertEq(a.withdrawableFree(LOT_ID, bidder1), aFreeBefore + N_BID_A, "C-01N: A committed not released");
        assertEq(a.withdrawableFree(LOT_ID, bidder1), N_CEILING_A, "C-01N: A free != full deposit");
        assertEq(a.withdrawableFree(LOT_ID, bidder2), bFreeBefore - nBidB, "C-01N: B free not debited by amount");
        assertEq(a.withdrawableFree(LOT_ID, bidder2), uint256(N_CEILING_A) - nBidB, "C-01N: B free != deposit - highBid");

        Lot memory lot = a.getLot(LOT_ID);
        assertEq(lot.highBidder, bidder2, "C-01N: highBidder not B");
        assertEq(uint256(lot.highBid), nBidB, "C-01N: highBid not B amount");

        // Conservation across the native rebalance.
        assertEq(_nativeBuckets(a, who), bucketsBefore, "C-01N: native bucket sum changed");
        assertEq(_nativeBuckets(a, who), balBefore, "C-01N: native buckets != contract balance");
    }

    // Self-outbid, same-slot ordering hazard: the standing top raises its own bid, so newTop == prevTop
    // and both _commitBid legs (commit newBid free->committed, then release prevTop's entire
    // committed->free) touch the SAME deposit slot. The only correct net end-state is committed == Y,
    // free == CEILING_A - Y: committing then releasing double-releases, releasing then committing strands
    // the new commit. The other rebalance tests use two distinct bidders, so this is the only coverage of
    // the aliased-slot case.
    function test_SelfOutbidRebalancesOwnDeposit() public {
        address[4] memory who = [bidder1, bidder2, seller, houseFeeRecipient];

        _initAndOpen(auctionT, address(token), RESERVE_TOKEN, uint64(block.timestamp + 1 days));
        _deposit(auctionT, address(token), bidder1, CEILING_A);

        // Opening bid X (bidIndex 0): bidder1 becomes the top with committed == X, free == CEILING_A - X.
        _placeBid(auctionT, bidder1, bidder1Key, 0, BID_A, 0, keccak256("qn-self-A"));
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder1), CEILING_A - BID_A, "C-01s: free after opening bid");
        assertEq(uint256(auctionT.getLot(LOT_ID).highBid), BID_A, "C-01s: highBid after opening bid");

        uint256 balBefore = token.balanceOf(address(auctionT));
        uint256 bucketsBefore = _erc20Buckets(auctionT, who);
        assertEq(bucketsBefore, balBefore, "C-01s: buckets != balance pre self-raise");

        // bidder1 self-raises to Y (bidIndex 1, observedPrevTop == own standing X). The released-from-
        // prior-top amount is bidder1's free after the self-release: CEILING_A - Y if correct, CEILING_A
        // if the new commit was double-released.
        uint128 selfRaise = BID_B; // 1500e6 > 1000e6, well over the 2% floor
        uint256 expectedFreeAfter = uint256(CEILING_A) - selfRaise;
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.BidPlaced(LOT_ID, bidder1, selfRaise, 2);
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.TopBidChanged(LOT_ID, bidder1, selfRaise);
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.BidEscrowCommitted(LOT_ID, bidder1, selfRaise, bidder1, uint128(expectedFreeAfter));
        _placeBid(auctionT, bidder1, bidder1Key, 1, selfRaise, BID_A, keccak256("qn-self-B"));

        // End-state: committed slice (deposit - free) == Y (not X+Y, not 0), free == CEILING_A - Y
        // (not CEILING_A, not CEILING_A - X - Y). Deposit total conserved.
        assertEq(
            auctionT.withdrawableFree(LOT_ID, bidder1),
            expectedFreeAfter,
            "C-01s: self-raise free != CEILING_A - Y (double-release or strand)"
        );
        uint256 committedSlice = uint256(CEILING_A) - auctionT.withdrawableFree(LOT_ID, bidder1);
        assertEq(committedSlice, uint256(selfRaise), "C-01s: committed slice != Y");

        Lot memory lot = auctionT.getLot(LOT_ID);
        assertEq(lot.highBidder, bidder1, "C-01s: highBidder not bidder1 after self-raise");
        assertEq(uint256(lot.highBid), selfRaise, "C-01s: highBid != Y");
        assertEq(uint256(committedSlice), uint256(lot.highBid), "C-01s: committed slice != lot.highBid");
        assertEq(uint256(lot.winnerSeq), 2, "C-01s: winnerSeq not the second bid seq");

        // No external transfer on a self-raise, and full bucket conservation: the deposit never grew,
        // only the locked slice moved from X to Y inside the same slot.
        assertEq(token.balanceOf(address(auctionT)), balBefore, "C-01s: contract balance moved on self-raise");
        assertEq(_erc20Buckets(auctionT, who), bucketsBefore, "C-01s: bucket sum changed on self-raise");
        assertEq(_erc20Buckets(auctionT, who), balBefore, "C-01s: buckets != balance after self-raise");
    }

    // Same-slot self-raise on a native-denominated clone, so a native-specific accounting regression in
    // _commitBid is not masked by the ERC-20 self-raise above. End-state: committed == Y, free ==
    // N_CEILING_A - Y, balance flat, winnerSeq == 2.
    function test_SelfOutbidRebalancesOwnDepositNative() public {
        address[4] memory who = [bidder1, bidder2, seller, houseFeeRecipient];

        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _initAndOpen(a, address(0), RESERVE_PRICE, uint64(block.timestamp + 1 days));
        _deposit(a, address(0), bidder1, N_CEILING_A);

        // Opening bid X == N_BID_A.
        _placeBid(a, bidder1, bidder1Key, 0, N_BID_A, 0, keccak256("qn-selfN-A"));
        assertEq(a.withdrawableFree(LOT_ID, bidder1), uint256(N_CEILING_A) - N_BID_A, "C-01sN: free after opening bid");

        uint256 balBefore = address(a).balance;
        uint256 bucketsBefore = _nativeBuckets(a, who);
        assertEq(bucketsBefore, balBefore, "C-01sN: buckets != balance pre self-raise");

        // Self-raise to Y == 2*N_BID_A (bidIndex 1, observedPrevTop == own N_BID_A).
        uint128 selfRaise = uint128(uint256(N_BID_A) * 2);
        uint256 expectedFreeAfter = uint256(N_CEILING_A) - selfRaise;
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.BidPlaced(LOT_ID, bidder1, selfRaise, 2);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.TopBidChanged(LOT_ID, bidder1, selfRaise);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.BidEscrowCommitted(LOT_ID, bidder1, selfRaise, bidder1, uint128(expectedFreeAfter));
        _placeBid(a, bidder1, bidder1Key, 1, selfRaise, uint128(N_BID_A), keccak256("qn-selfN-B"));

        assertEq(a.withdrawableFree(LOT_ID, bidder1), expectedFreeAfter, "C-01sN: self-raise free != N_CEILING_A - Y");
        uint256 committedSlice = uint256(N_CEILING_A) - a.withdrawableFree(LOT_ID, bidder1);
        assertEq(committedSlice, uint256(selfRaise), "C-01sN: committed slice != Y");

        Lot memory lot = a.getLot(LOT_ID);
        assertEq(lot.highBidder, bidder1, "C-01sN: highBidder not bidder1");
        assertEq(uint256(lot.highBid), selfRaise, "C-01sN: highBid != Y");
        assertEq(uint256(lot.winnerSeq), 2, "C-01sN: winnerSeq not the second bid seq");

        assertEq(address(a).balance, balBefore, "C-01sN: contract balance moved on self-raise");
        assertEq(_nativeBuckets(a, who), bucketsBefore, "C-01sN: native bucket sum changed on self-raise");
        assertEq(_nativeBuckets(a, who), balBefore, "C-01sN: native buckets != balance after self-raise");
    }

    // Minimal-increment rebalance: B outbids A at exactly _minBid (the 2% floor edge), so the committed
    // slice is the smallest valid next bid. The other rebalance tests jump far over the floor
    // (1000e6 -> 1500e6); this pins committed slice == accepted bid to the wei at the boundary, where
    // _minBid == highBid + Math.mulDiv(highBid, _minIncrementBps, 10_000).
    function test_CommitBidRebalancesAtMinIncrement() public {
        address[4] memory who = [bidder1, bidder2, seller, houseFeeRecipient];

        _initAndOpen(auctionT, address(token), RESERVE_TOKEN, uint64(block.timestamp + 1 days));
        _deposit(auctionT, address(token), bidder1, CEILING_A);
        _deposit(auctionT, address(token), bidder2, CEILING_B);

        // A opens at BID_A; B will outbid at EXACTLY the minimum valid increment over A.
        _placeBid(auctionT, bidder1, bidder1Key, 0, BID_A, 0, keccak256("qn-mi-A"));

        // bidB == A + 2% of A == 1020e6, the smallest amount that clears _minBid (one wei lower reverts
        // BidTooLow).
        uint128 increment = uint128(Math.mulDiv(uint256(BID_A), MIN_INCREMENT_BPS, 10_000));
        uint128 bidB = BID_A + increment;
        assertEq(uint256(bidB), uint256(BID_A) + Math.mulDiv(uint256(BID_A), MIN_INCREMENT_BPS, 10_000), "C-01mi: bidB != _minBid");

        uint256 balBefore = token.balanceOf(address(auctionT));
        uint256 bucketsBefore = _erc20Buckets(auctionT, who);
        assertEq(bucketsBefore, balBefore, "C-01mi: buckets != balance pre-outbid");

        // Outbid at the floor: the released-from-prior-top amount is A's free after A's committed
        // returned (CEILING_A).
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.BidPlaced(LOT_ID, bidder2, bidB, 2);
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.TopBidChanged(LOT_ID, bidder2, bidB);
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.BidEscrowCommitted(LOT_ID, bidder2, bidB, bidder1, CEILING_A);
        _placeBid(auctionT, bidder2, bidder2Key, 0, bidB, BID_A, keccak256("qn-mi-B"));

        // Committed slice == accepted bid to the wei at the floor: B.committed (deposit - free) == bidB,
        // and lot.highBid == bidB.
        Lot memory lot = auctionT.getLot(LOT_ID);
        assertEq(uint256(lot.highBid), uint256(bidB), "C-01mi: highBid != minimal-increment bid");
        uint256 committedSlice = uint256(CEILING_B) - auctionT.withdrawableFree(LOT_ID, bidder2);
        assertEq(committedSlice, uint256(bidB), "C-01mi: B committed slice != bidB at the increment floor");
        assertEq(committedSlice, uint256(lot.highBid), "C-01mi: committed slice != lot.highBid at the floor");
        assertEq(lot.highBidder, bidder2, "C-01mi: highBidder not B");

        // A fully released to free; no external transfer; full bucket conservation at the floor.
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder1), uint256(CEILING_A), "C-01mi: A not fully released");
        assertEq(token.balanceOf(address(auctionT)), balBefore, "C-01mi: contract balance moved at the floor");
        assertEq(_erc20Buckets(auctionT, who), bucketsBefore, "C-01mi: bucket sum changed at the floor");
        assertEq(_erc20Buckets(auctionT, who), balBefore, "C-01mi: buckets != balance after the floor rebalance");
    }

    // Fail-closed InsufficientFreeBalance on a native-denominated clone: free_B (N_BID_A - 1) < amount
    // (N_BID_A) reverts; no top recorded, free unchanged, no wei moved beyond the original deposit.
    function test_RevertWhen_InsufficientFreeBalanceNative() public {
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _initAndOpen(a, address(0), RESERVE_PRICE, uint64(block.timestamp + 1 days));

        // Fund exactly the reserve (RESERVE_PRICE == N_BID_A == 1 ether), then bid one wei over free.
        uint128 smallDeposit = uint128(RESERVE_PRICE); // == 1 ether, the reserve floor
        _deposit(a, address(0), bidder2, smallDeposit);

        uint128 bidAmt = smallDeposit + 1; // amount > free, but still a valid >= reserve bid
        uint256 balBefore = address(a).balance;

        vm.expectRevert(ISessionAuction.InsufficientFreeBalance.selector);
        _placeBid(a, bidder2, bidder2Key, 0, bidAmt, 0, keccak256("qn-BN"));

        // Fails closed: no top, free intact, no extra wei pulled.
        Lot memory lot = a.getLot(LOT_ID);
        assertEq(lot.highBidder, address(0), "C-02N: a top was recorded on revert");
        assertEq(uint256(lot.highBid), 0, "C-02N: highBid moved on revert");
        assertEq(a.withdrawableFree(LOT_ID, bidder2), smallDeposit, "C-02N: free changed on revert");
        assertEq(address(a).balance, balBefore, "C-02N: a spurious native pull occurred");
    }

    // _commitBid reverts InsufficientFreeBalance when free_B < amount; fails closed (top untouched, no
    // BidPlaced, no nonce consumed, no token pulled).
    function test_RevertWhen_InsufficientFreeBalance() public {
        _initAndOpen(auctionT, address(token), RESERVE_TOKEN, uint64(block.timestamp + 1 days));

        uint128 smallDeposit = BID_B - 1; // free_B < amount
        _deposit(auctionT, address(token), bidder2, smallDeposit);

        // amount (BID_B) >= _minBid (reserve, since no top yet) but free (BID_B - 1) < amount.
        uint256 contractBalBefore = token.balanceOf(address(auctionT));

        vm.expectRevert(ISessionAuction.InsufficientFreeBalance.selector);
        _placeBid(auctionT, bidder2, bidder2Key, 0, BID_B, 0, keccak256("qn-B"));

        // Fails closed: no top recorded, escrow untouched, free unchanged, no token pulled.
        Lot memory lot = auctionT.getLot(LOT_ID);
        assertEq(lot.highBidder, address(0), "C-02: a top was recorded on revert");
        assertEq(uint256(lot.highBid), 0, "C-02: highBid moved on revert");
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder2), smallDeposit, "C-02: free changed on revert");
        assertEq(token.balanceOf(address(auctionT)), contractBalBefore, "C-02: a spurious token pull occurred");

        // No nonce consumed by the failed bid: a retry by B at bidIndex 0 still authorizes. Top up so
        // the retry has free >= amount. This retry is the lot's first accepted bid, so it emits the
        // opening BidEscrowCommitted (prevTop == 0, released amount == 0) alongside BidPlaced(seq 1),
        // confirming the failed attempt left no partial top.
        _deposit(auctionT, address(token), bidder2, CEILING_B);
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.BidPlaced(LOT_ID, bidder2, BID_B, 1); // seq == 1: first ACCEPTED bid on the lot
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.BidEscrowCommitted(LOT_ID, bidder2, BID_B, address(0), 0);
        _placeBid(auctionT, bidder2, bidder2Key, 0, BID_B, 0, keccak256("qn-B2"));

        // The successful retry DID consume the keyed nonce: a third attempt re-using bidIndex 0 reverts
        // InvalidAccountNonce(bidder2, current) since the (principal, nonceKey) counter advanced to 1.
        // For a nonzero keyed nonce, `current` is the packed keyNonce ((key << 64) | 1), not the bare 1.
        // Top up first so this attempt cannot trip InsufficientFreeBalance and confound the cause.
        _deposit(auctionT, address(token), bidder2, CEILING_B);
        vm.expectRevert(
            abi.encodeWithSelector(Nonces.InvalidAccountNonce.selector, bidder2, _packedKeyNonce(bidder2, 1))
        );
        _placeBid(auctionT, bidder2, bidder2Key, 0, BID_B, BID_B, keccak256("qn-B3"));
    }

    // _lockEscrow is a single-shot snapshot at hammer only: winner.committed -> lot.escrowAmount,
    // committed zeroed; finalizeWinner must not re-lock.
    function test_LockEscrowSingleShot() public {
        uint64 endsAt = uint64(block.timestamp + 1 days);
        _initAndOpen(auctionT, address(token), RESERVE_TOKEN, endsAt);
        _deposit(auctionT, address(token), bidder1, CEILING_A);
        _placeBid(auctionT, bidder1, bidder1Key, 0, BID_A, 0, keccak256("qn-A"));

        // The snapshot is internal, so the contract balance is conserved across hammer.
        uint256 balBefore = token.balanceOf(address(auctionT));

        vm.warp(endsAt);
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.Hammered(LOT_ID, bidder1, BID_A);
        auctionT.hammer(LOT_ID);

        // After hammer: escrowAmount == BID_A (== winner.committed), committed zeroed, A's free
        // unchanged at CEILING_A - BID_A, phase Hammered.
        Lot memory lot = auctionT.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), BID_A, "C-03: escrowAmount != committed snapshot");
        assertEq(uint8(lot.phase), uint8(LotPhase.Hammered), "C-03: phase not Hammered");
        assertEq(uint256(lot.winnerSeq), 1, "C-03: winnerSeq not the winning bid seq");
        assertEq(
            auctionT.withdrawableFree(LOT_ID, bidder1),
            CEILING_A - BID_A,
            "C-03: winner free changed at lock"
        );
        // No transfer at hammer.
        assertEq(token.balanceOf(address(auctionT)), balBefore, "C-03: balance moved at hammer");

        // Single-shot guard: finalizeWinner (after the AC window) must NOT re-snapshot; it leaves
        // escrowAmount unchanged (a second _lockEscrow that zeroed it would later revert NoEscrow).
        // Reveal the winning bid first so finalize passes the reveal gate.
        vm.prank(bidder1);
        auctionT.reveal(LOT_ID, lot.winnerSeq, BID_A, bytes32("salt"));

        vm.warp(uint256(lot.hammeredAt) + AC_CHALLENGE_SEC + 1);
        auctionT.finalizeWinner(LOT_ID);

        Lot memory afterFinalize = auctionT.getLot(LOT_ID);
        assertEq(
            uint256(afterFinalize.escrowAmount),
            BID_A,
            "C-03: finalizeWinner re-locked (escrow zeroed/changed)"
        );
        assertEq(
            uint8(afterFinalize.deliveryState),
            uint8(DeliveryState.AwaitingDelivery),
            "C-03: finalize did not enter AwaitingDelivery"
        );
    }

    // depositCeiling denomination and top-up:
    //   (a) native: msg.value != amount (under and over) reverts WrongDenomination
    //   (b) ERC-20: msg.value != 0 reverts WrongDenomination
    //   (c) a repeat call tops up free; each emits CeilingDeposited(...newFree).

    // Native rail, msg.value != amount reverts WrongDenomination in both directions. The guard is `!=`
    // (not `<`), so over-send also reverts and strands no wei.
    function test_RevertWhen_DepositWrongDenominationNative() public {
        _initAndOpen(auctionN, address(0), RESERVE_PRICE, uint64(block.timestamp + 1 days));
        vm.deal(bidder1, uint256(N_CEILING_A) + 1);

        // under-send: amount says N_CEILING_A but only N_CEILING_A - 1 wei is sent.
        vm.expectRevert(ISessionAuction.WrongDenomination.selector);
        vm.prank(bidder1);
        auctionN.depositCeiling{value: N_CEILING_A - 1}(LOT_ID, N_CEILING_A);

        // over-send: one extra wei. A buggy `require(msg.value >= amount)` would silently strand the
        // extra wei and break balance conservation; the `!=` guard rejects it.
        vm.expectRevert(ISessionAuction.WrongDenomination.selector);
        vm.prank(bidder1);
        auctionN.depositCeiling{value: uint256(N_CEILING_A) + 1}(LOT_ID, N_CEILING_A);

        // No free credited and no wei stranded in the contract on either revert.
        assertEq(auctionN.withdrawableFree(LOT_ID, bidder1), 0, "C-04a: free credited on revert");
        assertEq(address(auctionN).balance, 0, "C-04a: wei stranded in contract on revert");
    }

    // ERC-20 rail, msg.value != 0 reverts WrongDenomination even with a valid approval (the ERC-20 _pull
    // branch requires msg.value == 0).
    function test_RevertWhen_DepositWrongDenominationERC20() public {
        _initAndOpen(auctionT, address(token), RESERVE_TOKEN, uint64(block.timestamp + 1 days));

        // A valid approval is in place, yet a nonzero msg.value reverts on the token-denominated rail.
        token.mint(bidder1, uint256(CEILING_A));
        vm.deal(bidder1, 1 wei);
        vm.startPrank(bidder1);
        token.approve(address(auctionT), CEILING_A);
        vm.expectRevert(ISessionAuction.WrongDenomination.selector);
        auctionT.depositCeiling{value: 1 wei}(LOT_ID, CEILING_A);
        vm.stopPrank();

        // No free credited and no token pulled on revert.
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder1), 0, "C-04b: free credited on revert");
        assertEq(token.balanceOf(address(auctionT)), 0, "C-04b: token pulled on revert");
    }

    // A repeat deposit tops up free; each emits CeilingDeposited with the running newFree, and the
    // contract pulls exactly the summed deposit via safeTransferFrom (token balance delta).
    function test_DepositTopUp() public {
        _initAndOpen(auctionT, address(token), RESERVE_TOKEN, uint64(block.timestamp + 1 days));

        uint128 first = 2_000e6;
        uint128 second = 1_500e6;
        uint256 balBefore = token.balanceOf(address(auctionT));

        token.mint(bidder1, uint256(first) + second);
        vm.startPrank(bidder1);
        token.approve(address(auctionT), uint256(first) + second);

        // First deposit: newFree == first.
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.CeilingDeposited(LOT_ID, bidder1, first, first);
        auctionT.depositCeiling(LOT_ID, first);

        // Second deposit (top-up): newFree == first + second.
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.CeilingDeposited(LOT_ID, bidder1, second, uint256(first) + second);
        auctionT.depositCeiling(LOT_ID, second);
        vm.stopPrank();

        // free accumulated; contract pulled exactly first + second via the ERC-20 safeTransferFrom.
        assertEq(
            auctionT.withdrawableFree(LOT_ID, bidder1),
            uint256(first) + second,
            "C-04c: top-up did not accumulate free"
        );
        assertEq(
            token.balanceOf(address(auctionT)) - balBefore,
            uint256(first) + second,
            "C-04c: contract did not pull the summed deposit via safeTransferFrom"
        );
    }

    // Native repeat-call top-up. Each depositCeiling{value:}(...) asserts msg.value == amount (the
    // native _pull, not safeTransferFrom) and emits CeilingDeposited with the running newFree;
    // address(a).balance grows by exactly the summed deposit.
    function test_DepositTopUpNative() public {
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _initAndOpen(a, address(0), RESERVE_PRICE, uint64(block.timestamp + 1 days));

        uint128 first = uint128(RESERVE_PRICE);          // 1 ether, clears the reserve floor
        uint128 second = uint128(RESERVE_PRICE) / 2;     // top-up need not re-clear the floor
        uint256 balBefore = address(a).balance;
        vm.deal(bidder1, uint256(first) + second);

        // First native deposit: newFree == first, msg.value == amount.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.CeilingDeposited(LOT_ID, bidder1, first, first);
        vm.prank(bidder1);
        a.depositCeiling{value: first}(LOT_ID, first);

        // Second native deposit (top-up): newFree == first + second.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.CeilingDeposited(LOT_ID, bidder1, second, uint256(first) + second);
        vm.prank(bidder1);
        a.depositCeiling{value: second}(LOT_ID, second);

        // free accumulated; the contract took EXACTLY first + second of native wei.
        assertEq(
            a.withdrawableFree(LOT_ID, bidder1),
            uint256(first) + second,
            "C-04cN: native top-up did not accumulate free"
        );
        assertEq(
            address(a).balance - balBefore,
            uint256(first) + second,
            "C-04cN: contract native balance != summed deposit"
        );
    }

    // Reserve-floor boundary at deposit: an exact-reserve deposit succeeds and credits free == RESERVE,
    // and a below-reserve deposit also succeeds (the reserve floor lives at placeBid, not at deposit).
    // Two principals so the prior free is untouched.
    function test_DepositAtReserveBoundary() public {
        _initAndOpen(auctionT, address(token), RESERVE_TOKEN, uint64(block.timestamp + 1 days));

        // Exact-reserve deposit succeeds and emits CeilingDeposited(...,RESERVE_TOKEN).
        token.mint(bidder1, uint256(RESERVE_TOKEN));
        vm.startPrank(bidder1);
        token.approve(address(auctionT), RESERVE_TOKEN);
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.CeilingDeposited(LOT_ID, bidder1, RESERVE_TOKEN, RESERVE_TOKEN);
        auctionT.depositCeiling(LOT_ID, RESERVE_TOKEN);
        vm.stopPrank();
        assertEq(
            auctionT.withdrawableFree(LOT_ID, bidder1),
            uint256(RESERVE_TOKEN),
            "C-08bd: exact-reserve deposit not credited to free"
        );

        // A strictly-below-reserve deposit also succeeds and credits free (the floor is at placeBid).
        uint128 belowReserve = RESERVE_TOKEN - 1;
        token.mint(bidder2, uint256(belowReserve));
        vm.startPrank(bidder2);
        token.approve(address(auctionT), belowReserve);
        auctionT.depositCeiling(LOT_ID, belowReserve);
        vm.stopPrank();
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder2), uint256(belowReserve), "C-08bd: below-reserve deposit not credited");
    }

    // Reserve-floor boundary on a native clone. The native deposit is pulled via msg.value == amount, so
    // a native-specific guard regression would be invisible on the ERC-20-only
    // test_DepositAtReserveBoundary. There is no deposit-time reserve floor: a sub-reserve deposit and an
    // exact-reserve deposit both succeed.
    function test_DepositAtReserveBoundaryNative() public {
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _initAndOpen(a, address(0), RESERVE_PRICE, uint64(block.timestamp + 1 days));

        // A sub-reserve deposit{value: belowReserve} succeeds and credits free (the floor is at placeBid).
        uint128 belowReserveN = uint128(RESERVE_PRICE) - 1;
        vm.deal(bidder1, uint256(belowReserveN));
        vm.prank(bidder1);
        a.depositCeiling{value: belowReserveN}(LOT_ID, belowReserveN);
        assertEq(a.withdrawableFree(LOT_ID, bidder1), uint256(belowReserveN), "C-08bdN: below-reserve native deposit not credited");

        // An exact-reserve native deposit succeeds and credits free == RESERVE_PRICE.
        uint128 exact = uint128(RESERVE_PRICE);
        vm.deal(bidder2, uint256(exact));
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.CeilingDeposited(LOT_ID, bidder2, exact, exact);
        vm.prank(bidder2);
        a.depositCeiling{value: exact}(LOT_ID, exact);
        assertEq(
            a.withdrawableFree(LOT_ID, bidder2),
            uint256(exact),
            "C-08bdN: exact-reserve native deposit not credited to free"
        );
        // The contract holds both accepted deposits (the sub-reserve deposit is not rejected).
        assertEq(address(a).balance, uint256(belowReserveN) + uint256(exact), "C-08bdN: native balance != the two accepted deposits");
    }

    // withdrawDeposit (nonReentrant, CEI) pulls up to current free; committed (the standing high bid) is
    // never withdrawable; over-withdraw and zero/no-free withdraw revert.

    // withdraw w <= free decrements free by w, committed unchanged, emits DepositWithdrawn.
    function test_WithdrawDepositUpToFree() public {
        _initAndOpen(auctionT, address(token), RESERVE_TOKEN, uint64(block.timestamp + 1 days));
        _deposit(auctionT, address(token), bidder1, CEILING_A);
        _placeBid(auctionT, bidder1, bidder1Key, 0, BID_A, 0, keccak256("qn-A"));

        uint128 freeBefore = CEILING_A - BID_A;
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder1), freeBefore, "C-05: free precondition");

        // Zero-amount guard: withdrawDeposit(lotId, 0) reverts NothingToWithdraw even with free
        // positive, so amount == 0 is rejected before any debit. Distinct from the no-free guard in
        // test_RevertWhen_WithdrawNothing.
        uint256 balBeforeZero = token.balanceOf(bidder1);
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auctionT.withdrawDeposit(LOT_ID, 0);
        assertEq(token.balanceOf(bidder1), balBeforeZero, "C-05: paid on a zero-amount withdraw");
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder1), freeBefore, "C-05: free moved on zero-amount withdraw");

        uint128 w = freeBefore; // pull the entire free slice, leaving committed intact
        uint256 bidderBalBefore = token.balanceOf(bidder1);

        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.DepositWithdrawn(LOT_ID, bidder1, w);

        vm.prank(bidder1);
        auctionT.withdrawDeposit(LOT_ID, w);

        // free drained to 0; committed is never withdrawable, so escrow behind A is untouched; bidder
        // received exactly w.
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder1), 0, "C-05: free not decremented by w");
        assertEq(token.balanceOf(bidder1), bidderBalBefore + w, "C-05: bidder not paid w");

        // committed stays locked: A is still the top, so a hammer would snapshot BID_A.
        Lot memory lot = auctionT.getLot(LOT_ID);
        assertEq(uint256(lot.highBid), BID_A, "C-05: committed high bid disturbed by free withdraw");
        assertEq(lot.highBidder, bidder1, "C-05: top bidder changed by free withdraw");
    }

    // Partial withdraw leaving a strictly-positive remainder. The other non-reverting withdrawDeposit
    // tests drain the entire free slice (w == free), which an impl that zeroes `free` wholesale instead
    // of doing `free -= w` would also pass while confiscating the remainder. This pins the strict
    // w < free path: a partial withdraw leaves a positive remainder, then a second drains it to 0.
    // ERC-20 rail, so the safeTransferFrom token delta == w is checked on each leg.
    function test_WithdrawDepositPartialLeavesRemainder() public {
        _initAndOpen(auctionT, address(token), RESERVE_TOKEN, uint64(block.timestamp + 1 days));
        _deposit(auctionT, address(token), bidder1, CEILING_A);
        _placeBid(auctionT, bidder1, bidder1Key, 0, BID_A, 0, keccak256("qn-A"));

        uint128 freeBefore = CEILING_A - BID_A;
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder1), freeBefore, "C-05p: free precondition");

        // w is strictly less than free (half), so a positive remainder survives. The strict-bound
        // asserts below keep this test from silently degrading into a full drain.
        uint128 w = freeBefore / 2;
        assertGt(uint256(w), 0, "C-05p: chosen partial w is not positive");
        assertLt(uint256(w), uint256(freeBefore), "C-05p: chosen partial w is not strictly below free");

        uint256 bidderBalBefore = token.balanceOf(bidder1);
        uint256 contractBalBefore = token.balanceOf(address(auctionT));

        // First partial withdraw: emits DepositWithdrawn(.,.,w) and subtracts w (does not zero free).
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.DepositWithdrawn(LOT_ID, bidder1, w);
        vm.prank(bidder1);
        auctionT.withdrawDeposit(LOT_ID, w);

        // free decremented by exactly w to a strictly positive remainder (a wholesale `free = 0` would
        // leave 0 here).
        uint256 remainder = uint256(freeBefore) - w;
        assertGt(remainder, 0, "C-05p: test misconfigured, remainder not positive");
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder1), remainder, "C-05p: free not decremented by w (wholesale-zeroed?)");
        // safeTransferFrom leg paid exactly w; contract released exactly w.
        assertEq(token.balanceOf(bidder1) - bidderBalBefore, w, "C-05p: bidder not paid exactly w on the first leg");
        assertEq(contractBalBefore - token.balanceOf(address(auctionT)), w, "C-05p: contract released != w on the first leg");

        // committed untouched by the partial free withdraw: A still the top, highBid still BID_A.
        Lot memory lot = auctionT.getLot(LOT_ID);
        assertEq(uint256(lot.highBid), BID_A, "C-05p: committed high bid disturbed by partial free withdraw");
        assertEq(lot.highBidder, bidder1, "C-05p: top bidder changed by partial free withdraw");

        // Second partial withdraw of the remainder drains free to 0, proving the first call subtracted
        // rather than confiscated (the remainder was still withdrawable).
        uint256 bidderBalMid = token.balanceOf(bidder1);
        uint256 contractBalMid = token.balanceOf(address(auctionT));
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.DepositWithdrawn(LOT_ID, bidder1, remainder);
        vm.prank(bidder1);
        auctionT.withdrawDeposit(LOT_ID, remainder);

        assertEq(auctionT.withdrawableFree(LOT_ID, bidder1), 0, "C-05p: remainder not drained to 0 on the second leg");
        assertEq(token.balanceOf(bidder1) - bidderBalMid, remainder, "C-05p: bidder not paid the remainder on the second leg");
        assertEq(contractBalMid - token.balanceOf(address(auctionT)), remainder, "C-05p: contract released != remainder on the second leg");
        // committed intact after both free legs: the high bid never moved.
        Lot memory afterBoth = auctionT.getLot(LOT_ID);
        assertEq(uint256(afterBoth.highBid), BID_A, "C-05p: committed disturbed across the two free withdraws");
        assertEq(afterBoth.highBidder, bidder1, "C-05p: top bidder changed across the two free withdraws");
        // Across both legs the bidder received exactly the full free slice (w + remainder == freeBefore),
        // no double-pay and no confiscation.
        assertEq(token.balanceOf(bidder1) - bidderBalBefore, uint256(freeBefore), "C-05p: total paid != full free slice");
    }

    // w > free reverts InsufficientFreeBalance (committed is never withdrawable).
    function test_RevertWhen_WithdrawExceedsFree() public {
        _initAndOpen(auctionT, address(token), RESERVE_TOKEN, uint64(block.timestamp + 1 days));
        _deposit(auctionT, address(token), bidder1, CEILING_A);
        _placeBid(auctionT, bidder1, bidder1Key, 0, BID_A, 0, keccak256("qn-A"));

        uint256 overByOne = uint256(CEILING_A - BID_A) + 1; // free + 1 (would dip into committed)
        uint256 bidderBalBefore = token.balanceOf(bidder1);

        vm.expectRevert(ISessionAuction.InsufficientFreeBalance.selector);
        vm.prank(bidder1);
        auctionT.withdrawDeposit(LOT_ID, overByOne);

        // Nothing paid out, committed untouched.
        assertEq(token.balanceOf(bidder1), bidderBalBefore, "C-05r: bidder paid on revert");
        assertEq(
            auctionT.withdrawableFree(LOT_ID, bidder1),
            CEILING_A - BID_A,
            "C-05r: free changed on revert"
        );
    }

    // After the full free slice is pulled (free == 0), a zero-amount withdraw reverts NothingToWithdraw
    // and a positive withdraw reverts InsufficientFreeBalance (committed cannot be drained via a double
    // call).
    function test_RevertWhen_WithdrawNothing() public {
        _initAndOpen(auctionT, address(token), RESERVE_TOKEN, uint64(block.timestamp + 1 days));
        _deposit(auctionT, address(token), bidder1, CEILING_A);
        _placeBid(auctionT, bidder1, bidder1Key, 0, BID_A, 0, keccak256("qn-A"));

        // Pull the entire free slice first, leaving free == 0 (committed BID_A still locked).
        uint128 freeSlice = CEILING_A - BID_A;
        vm.prank(bidder1);
        auctionT.withdrawDeposit(LOT_ID, freeSlice);
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder1), 0, "C-05n: free not fully drained");

        uint256 bidderBalBefore = token.balanceOf(bidder1);

        // A zero-amount withdraw against free == 0 reverts NothingToWithdraw.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auctionT.withdrawDeposit(LOT_ID, 0);

        // A second positive withdraw with no free left reverts InsufficientFreeBalance.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.InsufficientFreeBalance.selector);
        auctionT.withdrawDeposit(LOT_ID, 1);

        // Nothing paid out on either revert; committed (the standing top bid) intact.
        assertEq(token.balanceOf(bidder1), bidderBalBefore, "C-05n: bidder paid on a no-free withdraw");
        assertEq(uint256(auctionT.getLot(LOT_ID).highBid), BID_A, "C-05n: committed disturbed");
    }

    // claimPending (nonReentrant) drains the caller's failed-push credit via _pay, zeroing the slot
    // before the external call, and emits WithdrawalClaimed(account, amount).
    //
    // A successful claim needs a payee whose receive() accepts (else the claim's own push re-credits).
    // A toggling receiver rejects at release time (creating the credit) then accepts for the claim, so
    // the same contract is both the credit source and the claim payee. It plays the seller, since openLot
    // lets the test pick the seller identity while the buyer is bound to the ECDSA-signing bidder.
    function test_ClaimPending() public {
        // Drive a release to a toggling-receiver SELLER that rejects at release time, so _release parks
        // the seller proceeds in pending.
        C_TogglingReceiver sellerC = new C_TogglingReceiver();
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _driveToDelivered(a, address(sellerC), N_CEILING_A, N_BID_A);

        uint256 fee = Math.mulDiv(N_BID_A, FEE_BPS, 10_000);
        uint256 proceeds = uint256(N_BID_A) - fee;

        // Buyer (bidder1) confirms -> _release. The seller push fails and the proceeds are credited to
        // pending (WithdrawalCredited), not paid; the lot still settles.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(address(sellerC), proceeds);
        vm.prank(bidder1);
        a.confirmReceipt(LOT_ID, keccak256("photo"), "ipfs://photo");

        uint256 pending = a.pendingWithdrawal(address(sellerC));
        assertEq(pending, proceeds, "C-06: pending credit != released proceeds");

        // Native bucket conservation after the failed-push credit: the parked proceeds sit in the
        // seller's pending bucket and the fee left to the EOA feeRecipient.
        address[4] memory who = [bidder1, address(sellerC), seller, houseFeeRecipient];
        assertEq(_nativeBuckets(a, who), address(a).balance, "C-06: native buckets != balance after credit");

        // Toggle the receiver to accept and arm the CEI readback: claimPending must zero the slot before
        // the external call, so the receiver's mid-push read of its own pending sees 0.
        sellerC.setReject(false);
        sellerC.watch(address(a));
        uint256 contractBalBefore = address(a).balance;
        uint256 payeeBalBefore = address(sellerC).balance;

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(address(sellerC), pending);

        vm.prank(address(sellerC));
        a.claimPending();

        // CEI: the push fired and the slot was already zero when the receiver read it mid-push (zeroed
        // before the external call, not pay-then-zero).
        assertTrue(sellerC.sawPush(), "C-06: claim push never reached the receiver");
        assertEq(sellerC.pendingDuringPush(), 0, "C-06: pending NOT zeroed before the external push (CEI violated)");

        assertEq(a.pendingWithdrawal(address(sellerC)), 0, "C-06: pending not zeroed");
        assertEq(
            address(a).balance,
            contractBalBefore - pending,
            "C-06: contract did not pay out the pending credit"
        );
        assertEq(address(sellerC).balance - payeeBalBefore, pending, "C-06: payee not paid on claim");

        // Double-claim guard: a second claimPending by the same account reverts NothingToWithdraw and
        // pays nothing (the slot was zeroed before the pay and cannot be re-drained).
        uint256 balAfterDrain = address(a).balance;
        uint256 payeeAfterDrain = address(sellerC).balance;
        vm.prank(address(sellerC));
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        a.claimPending();
        assertEq(address(a).balance, balAfterDrain, "C-06: contract paid out on a second (empty) claim");
        assertEq(address(sellerC).balance, payeeAfterDrain, "C-06: payee re-paid on a second (empty) claim");
    }

    // claimPending() by an account with zero pending credit reverts NothingToWithdraw and pays nothing
    // (distinct from the post-drain double-claim above).
    function test_RevertWhen_ClaimPendingNothing() public {
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _initAndOpen(a, address(0), RESERVE_PRICE, uint64(block.timestamp + 1 days));

        // bidder3 never had a failed push, so its pending is 0.
        assertEq(a.pendingWithdrawal(bidder3), 0, "C-06e: precondition pending nonzero");
        uint256 contractBalBefore = address(a).balance;
        uint256 callerBalBefore = bidder3.balance;

        vm.prank(bidder3);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        a.claimPending();

        // No payout on the empty claim.
        assertEq(address(a).balance, contractBalBefore, "C-06e: contract paid out on an empty claim");
        assertEq(bidder3.balance, callerBalBefore, "C-06e: caller paid on an empty claim");
    }

    // _pay with pending-credit fallback. A failing native push (receive() reverts) credits the recipient
    // instead of reverting, emits WithdrawalCredited; escrow still leaves _release exactly once; the
    // seller is not paid and the contract retains the proceeds.
    function test_PayFailedPushCreditsPending() public {
        // Release to a SELLER whose receive() reverts. _release must not revert: it credits the seller's
        // pending balance and still zeroes escrow / settles the lot.
        C_RejectingReceiver sellerC = new C_RejectingReceiver();

        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _driveToDelivered(a, address(sellerC), N_CEILING_A, N_BID_A);

        uint256 fee = Math.mulDiv(N_BID_A, FEE_BPS, 10_000);
        uint256 proceeds = uint256(N_BID_A) - fee;

        uint256 sellerRawBefore = address(sellerC).balance;
        uint256 feeRecipBefore = houseFeeRecipient.balance;
        uint256 contractBalBefore = address(a).balance;

        // _pay credits the seller's pending (push failed), emits WithdrawalCredited(seller, proceeds);
        // the fee leg to the EOA feeRecipient still pays, and the lot still releases.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(address(sellerC), proceeds);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT_ID, address(sellerC), proceeds, fee);

        vm.prank(bidder1);
        a.confirmReceipt(LOT_ID, keccak256("photo"), "ipfs://photo");

        // Escrow left _release exactly once: escrowAmount zeroed, phase Settled, deliveryState Released.
        Lot memory settled = a.getLot(LOT_ID);
        assertEq(uint256(settled.escrowAmount), 0, "C-07: escrow not zeroed after release");
        assertEq(uint8(settled.phase), uint8(LotPhase.Settled), "C-07: phase not Settled");
        assertEq(uint8(settled.deliveryState), uint8(DeliveryState.Released), "C-07: not Released");

        // Proceeds sit in pending (not pushed): pending == proceeds, the seller's raw balance did not
        // increase, and the contract still holds the proceeds (only the fee left). The contract-retains
        // check catches a buggy impl that both credits and pays.
        assertEq(a.pendingWithdrawal(address(sellerC)), proceeds, "C-07: failed push not credited to pending");
        assertEq(address(sellerC).balance, sellerRawBefore, "C-07: seller raw balance moved (push should have failed)");
        assertEq(houseFeeRecipient.balance - feeRecipBefore, fee, "C-07: fee leg not paid");
        assertEq(contractBalBefore - address(a).balance, fee, "C-07: contract did not retain the parked proceeds");

        // Full native bucket conservation across the pay-with-pending fallback: escrowAmount is 0, the
        // proceeds sit in the seller's pending bucket, the fee left to the EOA feeRecipient. An impl that
        // credited pending but failed to retain the wei (or double-counted) breaks this even though the
        // point assertions pass.
        address[4] memory who = [bidder1, address(sellerC), seller, houseFeeRecipient];
        assertEq(_nativeBuckets(a, who), address(a).balance, "C-07: native bucket sum != balance after parked credit");
    }

    // Native gas-cap path: the seller's receive() does not revert but burns well over 50_000 gas, so it
    // succeeds only if the push forwards more than the cap. _pay pushes with call{value:, gas:50_000}, so
    // the burner runs out of gas, the push fails, and proceeds are credited to pending. Where
    // test_PayFailedPushCreditsPending only proves the revert fallback (which fails with or without a
    // cap), this pins the cap itself: an uncapped call would let the burner succeed and defeat the credit
    // fallback.
    function test_PayGasBurnerCreditsPending() public {
        // SELLER is a non-reverting receiver that consumes far more than 50_000 gas in receive().
        C_GasBurnReceiver sellerC = new C_GasBurnReceiver();

        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _driveToDelivered(a, address(sellerC), N_CEILING_A, N_BID_A);

        uint256 fee = Math.mulDiv(N_BID_A, FEE_BPS, 10_000);
        uint256 proceeds = uint256(N_BID_A) - fee;

        uint256 sellerRawBefore = address(sellerC).balance;
        uint256 feeRecipBefore = houseFeeRecipient.balance;
        uint256 contractBalBefore = address(a).balance;

        // Under the cap the burner's receive() runs out of gas, so the push fails and _pay credits the
        // seller's pending (no whole-call revert); emits WithdrawalCredited then Released. An uncapped
        // call would let the burner succeed, emitting no WithdrawalCredited and failing this expectEmit.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(address(sellerC), proceeds);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT_ID, address(sellerC), proceeds, fee);

        vm.prank(bidder1);
        a.confirmReceipt(LOT_ID, keccak256("photo"), "ipfs://photo");

        // Escrow left _release exactly once despite the gas-capped push: escrowAmount zeroed, phase
        // Settled, deliveryState Released (the lot settles regardless of push outcome).
        Lot memory settled = a.getLot(LOT_ID);
        assertEq(uint256(settled.escrowAmount), 0, "C-07g: escrow not zeroed after gas-capped release");
        assertEq(uint8(settled.phase), uint8(LotPhase.Settled), "C-07g: phase not Settled");
        assertEq(uint8(settled.deliveryState), uint8(DeliveryState.Released), "C-07g: not Released");

        // The burner was not paid (cap starved its receive()): proceeds in pending, seller raw balance
        // unchanged, fee leg to the EOA feeRecipient paid, contract retained the proceeds. An uncapped
        // call would let the burner succeed (pending == 0, seller raw balance += proceeds).
        assertEq(a.pendingWithdrawal(address(sellerC)), proceeds, "C-07g: gas-burner push not credited to pending (cap dropped?)");
        assertEq(address(sellerC).balance, sellerRawBefore, "C-07g: seller raw balance moved (cap let the burner succeed)");
        assertEq(houseFeeRecipient.balance - feeRecipBefore, fee, "C-07g: fee leg not paid");
        assertEq(contractBalBefore - address(a).balance, fee, "C-07g: contract did not retain the parked proceeds");

        // Full native bucket conservation across the gas-capped fallback: escrowAmount is 0, proceeds in
        // the seller's pending bucket, fee out to the EOA feeRecipient.
        address[4] memory who = [bidder1, address(sellerC), seller, houseFeeRecipient];
        assertEq(_nativeBuckets(a, who), address(a).balance, "C-07g: native bucket sum != balance after gas-capped credit");

        // The parked credit is recoverable: once it stops burning, the burner claims via the pull path
        // (a normal claimPending push is well under the cap), proving the cap parked but did not destroy.
        sellerC.setBurn(false);
        uint256 burnerBalBeforeClaim = address(sellerC).balance;
        uint256 contractBalBeforeClaim = address(a).balance;
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(address(sellerC), proceeds);
        vm.prank(address(sellerC));
        a.claimPending();
        assertEq(a.pendingWithdrawal(address(sellerC)), 0, "C-07g: pending not zeroed on the recovery claim");
        assertEq(address(sellerC).balance - burnerBalBeforeClaim, proceeds, "C-07g: burner not paid the parked proceeds on claim");
        assertEq(contractBalBeforeClaim - address(a).balance, proceeds, "C-07g: contract did not release the parked proceeds on claim");
    }

    // ERC-20 rail: _pay uses SafeERC20.trySafeTransfer; a token whose transfer() returns false (never
    // reverts) credits the recipient and emits WithdrawalCredited without reverting; escrow zeroed,
    // phase Settled, both legs (seller proceeds + fee) parked. MockERC20 cannot return false, so a local
    // false-returning token is used.
    function test_PayFailedPushCreditsPendingERC20() public {
        C_FalseReturningERC20 badToken = new C_FalseReturningERC20();

        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        uint64 endsAt = uint64(block.timestamp + 1 days);
        _initAndOpen(a, address(badToken), RESERVE_TOKEN, endsAt);

        // deposit + bid on the bad-token rail: transferFrom always succeeds, so the deposit pulls fine.
        badToken.mint(bidder1, uint256(CEILING_A));
        vm.prank(bidder1);
        badToken.approve(address(a), CEILING_A);
        vm.prank(bidder1);
        a.depositCeiling(LOT_ID, CEILING_A);
        _placeBid(a, bidder1, bidder1Key, 0, BID_A, 0, keccak256("qn-A"));

        vm.warp(endsAt);
        a.hammer(LOT_ID);

        uint64 wseq = a.getLot(LOT_ID).winnerSeq; // read before prank (inline getLot would consume it)
        vm.prank(bidder1);
        a.reveal(LOT_ID, wseq, BID_A, bytes32("salt"));

        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        a.finalizeWinner(LOT_ID);

        vm.prank(seller);
        a.markDelivered(LOT_ID, keccak256("proof"), "ipfs://proof");

        uint256 fee = Math.mulDiv(BID_A, FEE_BPS, 10_000);
        uint256 proceeds = uint256(BID_A) - fee;

        // With both push legs failing, nothing leaves the contract, so this balance is unchanged after.
        uint256 contractTokenBefore = badToken.balanceOf(address(a));

        // transfer() returns false at release time, so both _pay legs credit pending instead of reverting
        // (trySafeTransfer observes false and does not revert); the lot still settles.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(seller, proceeds);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(houseFeeRecipient, fee);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);

        vm.prank(bidder1);
        a.confirmReceipt(LOT_ID, keccak256("photo"), "ipfs://photo");

        Lot memory settled = a.getLot(LOT_ID);
        assertEq(uint256(settled.escrowAmount), 0, "C-07e: escrow not zeroed after release");
        assertEq(uint8(settled.phase), uint8(LotPhase.Settled), "C-07e: phase not Settled");
        assertEq(a.pendingWithdrawal(seller), proceeds, "C-07e: seller proceeds not parked");
        assertEq(a.pendingWithdrawal(houseFeeRecipient), fee, "C-07e: fee not parked");
        // No token left the contract on the failed pushes (escrow stays parked as credits).
        assertEq(badToken.balanceOf(seller), 0, "C-07e: seller paid despite false transfer");
        assertEq(badToken.balanceOf(houseFeeRecipient), 0, "C-07e: feeRecipient paid despite false transfer");
        // Contract-retains-proceeds: with both legs failed, the full proceeds + fee still back the parked
        // credits, so the contract token balance is unchanged. A _pay that misrouted/burned tokens on the
        // false branch yet still credited pending would pass the per-recipient zero checks but fail here.
        assertEq(
            badToken.balanceOf(address(a)),
            contractTokenBefore,
            "C-07e: contract token balance moved despite both pushes failing"
        );
        // The contract token balance is the parked escrow (proceeds + fee == BID_A) plus the winner's
        // unwithdrawn free remainder (CEILING_A - BID_A: bidder1 deposited CEILING_A but committed only
        // BID_A), so it equals CEILING_A.
        uint256 winnerFreeRemainder = uint256(CEILING_A) - uint256(BID_A);
        assertEq(proceeds + fee, uint256(BID_A), "C-07e: parked escrow (proceeds + fee) != BID_A");
        assertEq(a.withdrawableFree(LOT_ID, bidder1), winnerFreeRemainder, "C-07e: winner free remainder mismatch");
        assertEq(
            badToken.balanceOf(address(a)),
            proceeds + fee + winnerFreeRemainder,
            "C-07e: contract token != parked escrow (proceeds + fee) + winner free remainder"
        );
        assertEq(
            badToken.balanceOf(address(a)),
            uint256(CEILING_A),
            "C-07e: contract token != full deposited ceiling"
        );
    }

    // ERC-20 claimPending drain on the trySafeTransfer SUCCESS rail (the other claimPending drains here
    // run on the native call{gas:50_000} rail). Exercises the ERC-20 success leg of _pay
    // (trySafeTransfer == true) invoked from claimPending: park a credit via a false-returning transfer,
    // flip the token to succeed, claimPending(), then assert the slot is zeroed before the pay (CEI),
    // WithdrawalClaimed(account, proceeds) emitted, the token moved exactly, and a second claimPending
    // reverts NothingToWithdraw.
    function test_ClaimPendingERC20() public {
        C_FalseReturningERC20 badToken = new C_FalseReturningERC20();

        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        uint64 endsAt = uint64(block.timestamp + 1 days);
        _initAndOpen(a, address(badToken), RESERVE_TOKEN, endsAt);

        // deposit + bid on the bad-token rail (transferFrom always succeeds, so the deposit pulls fine).
        badToken.mint(bidder1, uint256(CEILING_A));
        vm.prank(bidder1);
        badToken.approve(address(a), CEILING_A);
        vm.prank(bidder1);
        a.depositCeiling(LOT_ID, CEILING_A);
        _placeBid(a, bidder1, bidder1Key, 0, BID_A, 0, keccak256("qn-A"));

        vm.warp(endsAt);
        a.hammer(LOT_ID);

        uint64 wseq = a.getLot(LOT_ID).winnerSeq; // read before prank (inline getLot would consume it)
        vm.prank(bidder1);
        a.reveal(LOT_ID, wseq, BID_A, bytes32("salt"));

        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        a.finalizeWinner(LOT_ID);

        vm.prank(seller);
        a.markDelivered(LOT_ID, keccak256("proof"), "ipfs://proof");

        uint256 fee = Math.mulDiv(BID_A, FEE_BPS, 10_000);
        uint256 proceeds = uint256(BID_A) - fee;

        // Release while transfer() returns false: both legs park to pending, the lot still settles.
        vm.prank(bidder1);
        a.confirmReceipt(LOT_ID, keccak256("photo"), "ipfs://photo");
        assertEq(a.pendingWithdrawal(seller), proceeds, "C-06erc: seller proceeds not parked pre-claim");
        assertEq(a.pendingWithdrawal(houseFeeRecipient), fee, "C-06erc: fee not parked pre-claim");
        // The full escrow backs the parked credits pre-claim, alongside the winner's unwithdrawn free
        // remainder (CEILING_A - BID_A), so the contract token balance == CEILING_A.
        uint256 winnerFreeRemainder = uint256(CEILING_A) - uint256(BID_A);
        assertEq(proceeds + fee, uint256(BID_A), "C-06erc: parked escrow (proceeds + fee) != BID_A");
        assertEq(a.withdrawableFree(LOT_ID, bidder1), winnerFreeRemainder, "C-06erc: winner free remainder mismatch");
        assertEq(
            badToken.balanceOf(address(a)),
            proceeds + fee + winnerFreeRemainder,
            "C-06erc: contract token != parked escrow (proceeds + fee) + winner free remainder"
        );
        assertEq(badToken.balanceOf(address(a)), uint256(CEILING_A), "C-06erc: contract token != full deposited ceiling");

        // Flip the token to a succeeding transfer so claimPending's trySafeTransfer returns true and the
        // token moves. The seller drains its parked proceeds via the pull path.
        badToken.setFail(false);
        uint256 contractTokenBefore = badToken.balanceOf(address(a));
        uint256 sellerTokenBefore = badToken.balanceOf(seller);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(seller, proceeds);

        vm.prank(seller);
        a.claimPending();

        // CEI: the slot is zeroed (a re-read sees 0); the token moved exactly proceeds on the success
        // rail, and the fee leg stays parked (only the seller's slot drained, not a wholesale sweep).
        assertEq(a.pendingWithdrawal(seller), 0, "C-06erc: pending not zeroed on the ERC-20 success drain");
        assertEq(
            badToken.balanceOf(seller) - sellerTokenBefore,
            proceeds,
            "C-06erc: payee not paid exactly proceeds on the trySafeTransfer success rail"
        );
        assertEq(
            contractTokenBefore - badToken.balanceOf(address(a)),
            proceeds,
            "C-06erc: contract did not release exactly proceeds on the success rail"
        );
        // The fee leg is untouched by the seller's claim: the contract still holds the parked fee plus the
        // winner's free remainder (only the seller's pending slot drained).
        assertEq(a.pendingWithdrawal(houseFeeRecipient), fee, "C-06erc: fee leg disturbed by the seller drain");
        assertEq(a.withdrawableFree(LOT_ID, bidder1), winnerFreeRemainder, "C-06erc: winner free remainder disturbed by the seller drain");
        assertEq(
            badToken.balanceOf(address(a)),
            fee + winnerFreeRemainder,
            "C-06erc: contract token != still-parked fee + winner free remainder after the drain"
        );

        // ERC-20 double-claim guard: a second claimPending by the now-empty account reverts
        // NothingToWithdraw and moves no token.
        uint256 contractAfterDrain = badToken.balanceOf(address(a));
        uint256 sellerAfterDrain = badToken.balanceOf(seller);
        vm.prank(seller);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        a.claimPending();
        assertEq(badToken.balanceOf(address(a)), contractAfterDrain, "C-06erc: contract paid on a second (empty) ERC-20 claim");
        assertEq(badToken.balanceOf(seller), sellerAfterDrain, "C-06erc: payee re-paid on a second (empty) ERC-20 claim");
    }

    // Fee truncation: _feeOf is Math.mulDiv(gross, _feeBps, 10_000), which floors, and the truncation
    // remainder (dust) goes to the seller inside proceeds. Uses an escrow where amount*FEE_BPS is not
    // divisible by 10_000 so a remainder arises. Beyond the per-recipient deltas and proceeds + fee ==
    // escrow, this checks the contract balance drops by exactly proceeds + fee (full escrow in two legs,
    // no wei stranded or minted), neither leg parked to pending, and the native-bucket equality holds
    // post-release.
    function test_PayFeeTruncationDustToSeller() public {
        // FEE_BPS == 250. Pick escrow == 1 ether + 1 wei so (escrow * 250) % 10_000 != 0.
        uint128 escrow = uint128(1 ether + 1);
        assertTrue((uint256(escrow) * FEE_BPS) % 10_000 != 0, "C-07d: chosen amount has no fee remainder");

        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _driveToDelivered(a, seller, escrow + 1 ether, escrow);

        uint256 fee = Math.mulDiv(escrow, FEE_BPS, 10_000);     // floored
        uint256 proceeds = uint256(escrow) - fee;               // seller captures the remainder
        assertEq(proceeds + fee, uint256(escrow), "C-07d: proceeds + fee != escrow (wei created/lost)");
        assertLe(fee * 10_000, uint256(escrow) * FEE_BPS, "C-07d: fee not floored");

        uint256 sellerBefore = seller.balance;
        uint256 feeRecipBefore = houseFeeRecipient.balance;
        // Snapshot the CONTRACT balance: with both legs paid to EOAs, exactly proceeds + fee must leave.
        uint256 contractBalBefore = address(a).balance;

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);

        vm.prank(bidder1);
        a.confirmReceipt(LOT_ID, keccak256("photo"), "ipfs://photo");

        // Seller captures the truncation remainder; feeRecipient gets the floored fee; escrow zeroed.
        assertEq(seller.balance - sellerBefore, proceeds, "C-07d: seller proceeds (incl dust) wrong");
        assertEq(houseFeeRecipient.balance - feeRecipBefore, fee, "C-07d: feeRecipient floored fee wrong");
        assertEq(uint256(a.getLot(LOT_ID).escrowAmount), 0, "C-07d: escrow not zeroed");

        // On-chain conservation: the full escrow left in exactly two legs (proceeds + fee). A split that
        // stranded or burned the odd truncation wei would show a drop of proceeds + fee +/- 1.
        assertEq(
            contractBalBefore - address(a).balance,
            proceeds + fee,
            "C-07d: contract balance did not drop by exactly proceeds + fee (dust stranded/burned/minted)"
        );
        // Neither leg parked: both recipients are accepting EOAs, so a correct _release pushes both. A
        // stranded-dust impl that parked the odd wei to pending would trip one of these.
        assertEq(a.pendingWithdrawal(seller), 0, "C-07d: seller leg parked to pending on the dust path");
        assertEq(a.pendingWithdrawal(houseFeeRecipient), 0, "C-07d: fee leg parked to pending on the dust path");

        // Full native bucket conservation post-release: escrowAmount is 0, both legs left to EOAs, and the
        // winner's free slack (deposit - escrow == 1 ether) is still tracked.
        address[4] memory who = [bidder1, seller, houseFeeRecipient, bidder2];
        assertEq(_nativeBuckets(a, who), address(a).balance, "C-07d: native buckets != balance after the dust split");
    }

    // Below-reserve deposits and second-escrow-exit guards.

    // There is no deposit-time reserve floor (a deposit only funds `free`; the floor is at placeBid via
    // BidTooLow), so a below-reserve deposit succeeds and credits free. The DepositBelowReserve error is
    // vestigial with no use-site.
    function test_DepositBelowReserveIsAllowed() public {
        _initAndOpen(auctionT, address(token), RESERVE_TOKEN, uint64(block.timestamp + 1 days));

        // A strictly-below-reserve deposit is accepted (it simply cannot, on its own, fund a winning bid).
        uint128 belowReserve = RESERVE_TOKEN - 1;

        token.mint(bidder1, uint256(belowReserve));
        vm.startPrank(bidder1);
        token.approve(address(auctionT), belowReserve);
        vm.expectEmit(true, true, true, true, address(auctionT));
        emit ISessionAuction.CeilingDeposited(LOT_ID, bidder1, belowReserve, belowReserve);
        auctionT.depositCeiling(LOT_ID, belowReserve);
        vm.stopPrank();

        // free credited and token pulled: the reserve floor lives at placeBid, not deposit.
        assertEq(auctionT.withdrawableFree(LOT_ID, bidder1), uint256(belowReserve), "C-08a: below-reserve deposit not credited");
        assertEq(token.balanceOf(address(auctionT)), uint256(belowReserve), "C-08a: below-reserve deposit not pulled");
    }

    // On a Settled lot the first guard in releaseAfterWindow is the delivery-state check (it requires
    // Delivered), so a re-call reverts WrongDeliveryState (not EscrowAlreadyReleased). No escrow exit
    // fires twice.
    function test_RevertWhen_ReleaseAfterWindowOnSettledLot() public {
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _driveToDelivered(a, seller, N_CEILING_A, N_BID_A);

        vm.prank(bidder1);
        a.confirmReceipt(LOT_ID, keccak256("photo"), "ipfs://photo"); // -> Released/Settled

        Lot memory settled = a.getLot(LOT_ID);
        assertEq(uint256(settled.escrowAmount), 0, "C-08b: escrow not zeroed after first release");
        assertEq(uint8(settled.phase), uint8(LotPhase.Settled), "C-08b: phase not Settled");

        // A second release on the Settled lot reverts on the delivery-state guard (deliveryState is
        // Released, not Delivered), not the spent-escrow guard.
        uint256 contractBalBefore = address(a).balance;
        vm.warp(uint256(settled.deliveredAt) + DISPUTE_WINDOW_SEC);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        a.releaseAfterWindow(LOT_ID);

        // No second escrow exit fired: contract balance unchanged by the rejected second release.
        assertEq(address(a).balance, contractBalBefore, "C-08b: a second escrow exit paid out");
    }

    // No-double-pay on the winner escrow. The escrow exits via EITHER the reclaim _refund OR
    // withdrawRefund (when the session is voided), both zeroing the same lot.escrowAmount slot, so
    // exactly one fires and the second attempt pays nothing.
    //
    // EscrowAlreadyReleased guards Treasury.resolveForfeit, not withdrawRefund. withdrawRefund tallies
    // the caller's free+committed, then the winner escrow iff lot.escrowAmount != 0, then the dispute
    // bond, and reverts NothingToWithdraw when the running amount is 0. So with free/committed == 0 and
    // the escrow already spent, the second exit surfaces as NothingToWithdraw before any _pay.
    //
    // To make that NothingToWithdraw unconfounded, the winner first withdraws all free slack, the lot is
    // Refunded via the reclaim path (escrowAmount zeroed), then voidSession is called so withdrawRefund
    // passes its session-voided gate.
    function test_RevertWhen_EscrowAlreadyReleased() public {
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _driveToAwaiting(a, seller, N_CEILING_A, N_BID_A);

        // Winner drains all free slack first (committed was snapshotted into escrowAmount at hammer), so
        // free == 0 and committed == 0.
        uint128 freeSlice = N_CEILING_A - N_BID_A;
        vm.prank(bidder1);
        a.withdrawDeposit(LOT_ID, freeSlice);
        assertEq(a.withdrawableFree(LOT_ID, bidder1), 0, "C-08b2: winner free not drained");

        // Seller never delivers; buyer reclaims after the deliver window -> Refunded via _refund, which
        // zeroes lot.escrowAmount.
        uint256 awaitingAt = uint256(a.getLot(LOT_ID).awaitingAt);
        vm.warp(awaitingAt + SELLER_DELIVER_SEC);
        vm.prank(bidder1);
        a.reclaimUndelivered(LOT_ID);

        Lot memory refunded = a.getLot(LOT_ID);
        assertEq(uint256(refunded.escrowAmount), 0, "C-08b2: escrow not zeroed by _refund");
        assertEq(uint8(refunded.phase), uint8(LotPhase.Refunded), "C-08b2: phase not Refunded");

        // Void the session so the withdrawRefund session-voided gate passes; with free/committed == 0 the
        // winner-escrow leg is the only contributor and finds escrow spent.
        vm.prank(address(hammer));
        a.voidSession("post-mortem");

        uint256 contractBalBefore = address(a).balance;
        vm.prank(bidder1);
        // Spent escrow + drained free/committed -> withdrawRefund finds amount == 0 -> NothingToWithdraw
        // (EscrowAlreadyReleased is a Treasury-only guard, never reached here).
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        a.withdrawRefund(LOT_ID);

        // No second escrow exit fired against the already-spent slot.
        assertEq(address(a).balance, contractBalBefore, "C-08b2: a second escrow exit paid out");
        // Touch-nothing: the reverted withdrawRefund left free and committed at 0 and credited nothing to
        // pending (fail-closed at the slot level, not just net).
        assertEq(a.withdrawableFree(LOT_ID, bidder1), 0, "C-08b2: free moved on the reverted withdrawRefund");
        assertEq(a.pendingWithdrawal(bidder1), 0, "C-08b2: pending credited on the reverted withdrawRefund");
    }

    // Reentrancy backbone: withdrawDeposit and claimPending are nonReentrant, the native-push attack
    // surface. The reentrant inner call reverts ReentrancyGuardReentrantCall, but that revert is
    // swallowed into the pending-credit fallback, so a single outer call can resolve either way (paid
    // out, or re-credited). Two assertions:
    //   (1) the inner reentrant call was rejected by the guard (the receiver records the selector);
    //   (2) no double-pay: paidOut + stillCredited == amount and paidOut <= amount, however the outer
    //       push resolved.
    // The receiver records the inner-revert selector then returns (does not propagate) so the outer push
    // completes.

    // Reentrant claimPending: a payee with a pending credit reenters claimPending() from receive().
    function test_RevertWhen_ReentrantClaimPending() public {
        C_ReentrantClaimer attacker = new C_ReentrantClaimer();

        // Create a pending credit for `attacker`: it is the SELLER, disarmed at release time so receive()
        // reverts, failing the release push and parking the proceeds to pending.
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        attacker.arm(address(a), false);
        _driveToDelivered(a, address(attacker), N_CEILING_A, N_BID_A);

        uint256 fee = Math.mulDiv(N_BID_A, FEE_BPS, 10_000);
        uint256 proceeds = uint256(N_BID_A) - fee;

        vm.prank(bidder1);
        a.confirmReceipt(LOT_ID, keccak256("photo"), "ipfs://photo");
        assertEq(a.pendingWithdrawal(address(attacker)), proceeds, "RC: credit not parked");

        // Arm the reentrancy: on the next inbound push, receive() reenters claimPending() once, records
        // the guard revert, then returns.
        attacker.arm(address(a), true);
        uint256 contractBalBefore = address(a).balance;
        uint256 attackerBalBefore = address(attacker).balance;

        // Outer claim: zeroes pending (CEI), pushes to the attacker. The reentrant inner claimPending()
        // hits the nonReentrant guard (modifier before body) and reverts ReentrancyGuardReentrantCall.
        vm.prank(address(attacker));
        a.claimPending();

        // (1) the reentrant inner call was rejected by the guard.
        assertEq(
            attacker.lastReentryError(),
            ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector,
            "RC: reentrant claimPending not blocked by the guard"
        );
        // (2) no double-pay: the proceeds are accounted EXACTLY once across the outer call.
        uint256 paidOut = address(attacker).balance - attackerBalBefore;
        uint256 stillCredited = a.pendingWithdrawal(address(attacker));
        assertEq(paidOut + stillCredited, proceeds, "RC: amount not conserved across reentrant claim");
        assertLe(paidOut, proceeds, "RC: payee double-paid");
        assertEq(contractBalBefore - address(a).balance, paidOut, "RC: contract debit != amount paid out");

        // (3) Full native bucket conservation however the outer claim resolved: the proceeds are either
        //     in the attacker's pocket or back in its pending bucket, the winner's free slack is still
        //     tracked, and the fee left to the EOA feeRecipient.
        address[4] memory who = [bidder1, address(attacker), seller, houseFeeRecipient];
        assertEq(_nativeBuckets(a, who), address(a).balance, "RC: native bucket sum != balance after reentrant claim");
    }

    // Reentrant withdrawDeposit: a depositor-contract with free deposit reenters withdrawDeposit() from
    // receive() during the gas-capped push.
    function test_RevertWhen_ReentrantWithdrawDeposit() public {
        C_ReentrantWithdrawer attacker = new C_ReentrantWithdrawer();

        // The attacker funds a native deposit (no signature needed). free == deposit, committed == 0
        // (it never bid), so the whole slice is withdrawable.
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _initAndOpen(a, address(0), RESERVE_PRICE, uint64(block.timestamp + 1 days));

        uint128 deposit = N_CEILING_A;
        vm.deal(address(attacker), uint256(deposit));
        vm.prank(address(attacker));
        a.depositCeiling{value: deposit}(LOT_ID, deposit);
        assertEq(a.withdrawableFree(LOT_ID, address(attacker)), deposit, "RW: deposit not credited to free");

        uint128 w = deposit; // withdraw the whole free slice
        attacker.arm(address(a), LOT_ID, w);
        uint256 contractBalBefore = address(a).balance;
        uint256 attackerBalBefore = address(attacker).balance;

        // Outer withdraw: debits free (CEI), pushes w. The reentrant inner withdrawDeposit() hits the
        // nonReentrant guard and reverts ReentrancyGuardReentrantCall; the receiver records it.
        vm.prank(address(attacker));
        a.withdrawDeposit(LOT_ID, w);

        // (1) the reentrant inner call was rejected by the guard.
        assertEq(
            attacker.lastReentryError(),
            ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector,
            "RW: reentrant withdrawDeposit not blocked by the guard"
        );
        // (2) no double-withdraw: free was debited by w before the push (CEI), so it stays 0; the push
        //     either delivered w or re-credited it. The attacker never gets more than w.
        uint256 paidOut = address(attacker).balance - attackerBalBefore;
        uint256 credited = a.pendingWithdrawal(address(attacker));
        assertEq(a.withdrawableFree(LOT_ID, address(attacker)), 0, "RW: free not debited exactly once");
        assertEq(paidOut + credited, w, "RW: amount not conserved across reentrant withdraw");
        assertLe(paidOut, w, "RW: payee double-paid");
        assertEq(contractBalBefore - address(a).balance, paidOut, "RW: contract debit != amount paid out");

        // (3) CEI: the receiver read its own free mid-push and it was already 0, proving withdrawDeposit
        //     debits free before the external call (not pay-then-debit).
        assertEq(attacker.freeDuringPush(), 0, "RW: free NOT debited before the external push (CEI violated)");

        // (4) Full native bucket conservation: the attacker is the only funder, so buckets == balance
        //     whether the outer push delivered w or re-credited it.
        address[4] memory who = [address(attacker), bidder1, seller, houseFeeRecipient];
        assertEq(_nativeBuckets(a, who), address(a).balance, "RW: native bucket sum != balance after reentrant withdraw");
    }

    // Reentrancy backbone, the escrow-MOVING exits. Unlike the deposit/credit tests above, these move
    // the winner escrow: the property is that the winner escrow leaves exactly once even under a
    // cross-function reentry during the native proceeds push. A malicious SELLER-receiver (installed via
    // the openLot seller arg) reenters a second escrow-exit (confirmReceipt <-> releaseAfterWindow) on
    // the inbound _release push. The guard must reject the inner call; the receiver records the selector
    // and returns so the outer push resolves; escrow must have left exactly once (escrowAmount == 0,
    // phase Settled, balance dropped by at most proceeds + fee, full native bucket conservation).
    // confirmReceipt and releaseAfterWindow are not reentry-tested elsewhere.

    // confirmReceipt -> _release proceeds push reenters releaseAfterWindow (cross-function second exit).
    function test_RevertWhen_ReentrantConfirmReceipt() public {
        C_ReentrantSeller sellerC = new C_ReentrantSeller();

        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        // On the inbound proceeds push, reenter releaseAfterWindow(LOT_ID) once (a different escrow-exit
        // than the outer confirmReceipt). The receiver accepts the value so the outer _release succeeds
        // and escrow leaves exactly once.
        sellerC.arm(address(a), abi.encodeWithSignature("releaseAfterWindow(uint256)", LOT_ID));
        _driveToDelivered(a, address(sellerC), N_CEILING_A, N_BID_A);

        uint256 fee = Math.mulDiv(N_BID_A, FEE_BPS, 10_000);
        uint256 proceeds = uint256(N_BID_A) - fee;
        uint256 contractBalBefore = address(a).balance;

        // Outer confirmReceipt: CEI zeroes escrow + sets Settled before the proceeds push; the reentrant
        // releaseAfterWindow hits the nonReentrant guard and reverts ReentrancyGuardReentrantCall.
        vm.prank(bidder1);
        a.confirmReceipt(LOT_ID, keccak256("photo"), "ipfs://photo");

        // (1) the cross-function reentrant call was rejected by the guard.
        assertEq(
            sellerC.lastReentryError(),
            ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector,
            "RConf: cross-function reentry into releaseAfterWindow not blocked by the guard"
        );
        // (2) escrow left exactly once: zeroed, phase Settled, balance dropped by at most proceeds+fee,
        //     seller paid proceeds, feeRecipient paid fee.
        Lot memory settled = a.getLot(LOT_ID);
        assertEq(uint256(settled.escrowAmount), 0, "RConf: escrow not zeroed (or re-entered exit moved it)");
        assertEq(uint8(settled.phase), uint8(LotPhase.Settled), "RConf: phase not Settled exactly once");
        assertEq(uint8(settled.deliveryState), uint8(DeliveryState.Released), "RConf: not Released");
        assertLe(contractBalBefore - address(a).balance, proceeds + fee, "RConf: more than one escrow exit left the contract");
        assertEq(address(sellerC).balance, proceeds, "RConf: seller not paid proceeds exactly once");
        assertEq(a.pendingWithdrawal(address(sellerC)), 0, "RConf: a second exit parked extra proceeds");

        // (3) Full native bucket conservation: escrow gone, seller proceeds and fee left to EOAs, winner
        //     free still tracked.
        address[4] memory who = [bidder1, address(sellerC), seller, houseFeeRecipient];
        assertEq(_nativeBuckets(a, who), address(a).balance, "RConf: native bucket sum != balance after reentrant release");
    }

    // releaseAfterWindow -> _release proceeds push reenters confirmReceipt (cross-function second exit).
    function test_RevertWhen_ReentrantReleaseAfterWindow() public {
        C_ReentrantSeller sellerC = new C_ReentrantSeller();

        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        // On the inbound push, reenter confirmReceipt(LOT_ID, ...) once. confirmReceipt is `onlyBuyer
        // nonReentrant` and Solidity runs modifiers left-to-right, so onlyBuyer runs first. The reentrant
        // caller is the seller-receiver, not the lot.highBidder, so onlyBuyer reverts Unauthorized()
        // before the nonReentrant guard is reached; the second escrow exit is still blocked. The receiver
        // accepts the value so the outer push completes and escrow leaves exactly once.
        sellerC.arm(address(a), abi.encodeWithSignature("confirmReceipt(uint256,bytes32,string)", LOT_ID, keccak256("x"), "ipfs://x"));
        _driveToDelivered(a, address(sellerC), N_CEILING_A, N_BID_A);

        uint256 fee = Math.mulDiv(N_BID_A, FEE_BPS, 10_000);
        uint256 proceeds = uint256(N_BID_A) - fee;

        // Advance to the auto-release window and trigger the PERMISSIONLESS releaseAfterWindow.
        Lot memory delivered = a.getLot(LOT_ID);
        vm.warp(uint256(delivered.deliveredAt) + DISPUTE_WINDOW_SEC);
        uint256 contractBalBefore = address(a).balance;

        // The outer releaseAfterWindow CEI zeroes escrow + Settles before the proceeds push; the reentrant
        // confirmReceipt is rejected by onlyBuyer (the seller-receiver is not the buyer) before the
        // nonReentrant guard, reverting Unauthorized().
        a.releaseAfterWindow(LOT_ID);

        // (1) the cross-function reentrant call was rejected by onlyBuyer (Unauthorized), which runs
        //     before the nonReentrant guard, so the second escrow exit is blocked.
        assertEq(
            sellerC.lastReentryError(),
            ISessionAuction.Unauthorized.selector,
            "RRel: cross-function reentry into confirmReceipt not blocked (expected onlyBuyer Unauthorized)"
        );
        // (2) escrow left EXACTLY ONCE.
        Lot memory settled = a.getLot(LOT_ID);
        assertEq(uint256(settled.escrowAmount), 0, "RRel: escrow not zeroed (or re-entered exit moved it)");
        assertEq(uint8(settled.phase), uint8(LotPhase.Settled), "RRel: phase not Settled exactly once");
        assertEq(uint8(settled.deliveryState), uint8(DeliveryState.Released), "RRel: not Released");
        assertLe(contractBalBefore - address(a).balance, proceeds + fee, "RRel: more than one escrow exit left the contract");
        assertEq(address(sellerC).balance, proceeds, "RRel: seller not paid proceeds exactly once");
        assertEq(a.pendingWithdrawal(address(sellerC)), 0, "RRel: a second exit parked extra proceeds");

        // (3) FULL NATIVE BUCKET CONSERVATION.
        address[4] memory who = [bidder1, address(sellerC), seller, houseFeeRecipient];
        assertEq(_nativeBuckets(a, who), address(a).balance, "RRel: native bucket sum != balance after reentrant release");
    }

    // reclaimUndelivered -> _refund pays the BUYER; a hostile ERC-1271 buyer reenters withdrawRefund on
    // the inbound refund push (the buyer-side escrow-exit reentry). The winner escrow must refund exactly
    // once: the second exit is rejected by the nonReentrant guard.
    function test_RevertWhen_ReentrantReclaimUndelivered() public {
        // The buyer is an ERC-1271 contract whose isValidSignature recovers to bidder1 (so the bid signed
        // with bidder1Key authorizes), and whose receive() reenters withdrawRefund(LOT_ID) once on the
        // inbound refund push, records the guard revert, then returns (accepting the value).
        C_ReentrantBuyer buyer = new C_ReentrantBuyer(bidder1);

        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        buyer.arm(address(a), abi.encodeWithSignature("withdrawRefund(uint256)", LOT_ID));
        _driveToAwaitingWithBuyer(a, address(buyer));

        uint128 escrow = N_BID_A; // full escrow refunds to the buyer, NO fee
        uint256 contractBalBefore = address(a).balance;

        // Seller never delivers; the buyer reclaims after the deliver window. The outer reclaim CEI
        // zeroes escrow + sets Refunded before the refund push; the reentrant withdrawRefund hits the
        // nonReentrant guard and reverts ReentrancyGuardReentrantCall.
        uint256 awaitingAt = uint256(a.getLot(LOT_ID).awaitingAt);
        vm.warp(awaitingAt + SELLER_DELIVER_SEC);
        vm.prank(address(buyer));
        a.reclaimUndelivered(LOT_ID);

        // (1) the buyer-side reentrant call was rejected by the guard.
        assertEq(
            buyer.lastReentryError(),
            ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector,
            "RRec: buyer reentry into withdrawRefund not blocked by the guard"
        );
        // (2) escrow refunded exactly once: zeroed, phase Refunded, full escrow paid to the buyer (no
        //     fee), balance dropped by at most the escrow, nothing parked to pending.
        Lot memory refunded = a.getLot(LOT_ID);
        assertEq(uint256(refunded.escrowAmount), 0, "RRec: escrow not zeroed (or re-entered exit moved it)");
        assertEq(uint8(refunded.phase), uint8(LotPhase.Refunded), "RRec: phase not Refunded exactly once");
        assertEq(uint8(refunded.deliveryState), uint8(DeliveryState.Refunded), "RRec: not Refunded");
        assertLe(contractBalBefore - address(a).balance, uint256(escrow), "RRec: more than one escrow exit left the contract");
        assertEq(address(buyer).balance, uint256(escrow), "RRec: buyer not refunded the full escrow exactly once");
        assertEq(a.pendingWithdrawal(address(buyer)), 0, "RRec: a second exit parked extra refund");

        // (3) Full native bucket conservation: escrow gone, refunded to the buyer, winner free was 0
        //     (deposit == bid).
        address[4] memory who = [address(buyer), bidder1, seller, houseFeeRecipient];
        assertEq(_nativeBuckets(a, who), address(a).balance, "RRec: native bucket sum != balance after reentrant reclaim");
    }
}

// Local test doubles (C_ prefixed so they never collide with symbols in other domain files).

/// @notice A receiver whose native fallback always reverts, so any gas-capped `_pay` push to it fails
///         and falls back to a pending credit. It can still hold a deposit and act as a
///         bidder/seller/buyer for the pre-state build.
contract C_RejectingReceiver {
    receive() external payable {
        revert("reject");
    }
}

/// @notice A receiver whose native fallback does NOT revert but burns far more than the 50_000-gas cap,
///         distinguishing the capped `call{value:, gas:50_000}` from an uncapped call. As the SELLER,
///         its receive() runs out of gas inside the capped frame, so the push fails and _pay credits
///         pending. While `burn == true` it writes a bounded loop of distinct cold storage slots
///         (~22_100 gas each), so a handful blow past the cap; toggling `burn` off makes receive() a
///         cheap no-op so the recovery claimPending push succeeds.
contract C_GasBurnReceiver {
    bool public burn = true;
    uint256 private nonce;                  // advances so each call writes to fresh, cold slots
    mapping(uint256 => uint256) private sink; // distinct cold slots; cold SSTORE ~22_100 gas each

    function setBurn(bool v) external {
        burn = v;
    }

    receive() external payable {
        if (!burn) return; // disarmed: accept the value cheaply (recovery claimPending succeeds)
        // Bounded loop of cold SSTOREs: 64 * ~22_100 gas far exceeds the cap, so the capped push reverts
        // out-of-gas after ~2 iterations. Each write targets a fresh slot (base + i under an advancing
        // nonce), so it stays cold and cannot be elided.
        uint256 base = (nonce++) * 1_000 + 1;
        for (uint256 i = 0; i < 64; i++) {
            sink[base + i] = base + i + 1;
        }
    }
}

/// @notice A receiver that rejects while `reject == true` and accepts once toggled. The credit is
///         created while rejecting (failed push -> pending); after toggling, claimPending succeeds, so
///         the same contract is both the credit source and the claim payee.
///
///         For the CEI zero-before-pay proof, when accepting it reads back its own
///         pendingWithdrawal(self) during the inbound push: a CEI claimPending zeroes the slot before
///         the external call, so the recorded value must be 0. The read is a staticcall, so it does not
///         trip the reentrancy guard.
contract C_TogglingReceiver {
    bool public reject = true;
    address public observed;     // auction to read pending from during an accepting push (0 == skip)
    bool public sawPush;         // an accepting push actually fired
    uint256 public pendingDuringPush; // pendingWithdrawal(self) observed mid-push (CEI: must be 0)

    function setReject(bool v) external {
        reject = v;
    }

    function watch(address auction) external {
        observed = auction;
    }

    receive() external payable {
        if (reject) revert("no ether");
        if (observed != address(0)) {
            sawPush = true;
            // Read our own pending mid-push; CEI requires it already zeroed before this external call.
            (bool ok, bytes memory ret) =
                observed.staticcall(abi.encodeWithSignature("pendingWithdrawal(address)", address(this)));
            if (ok && ret.length == 32) {
                pendingDuringPush = abi.decode(ret, (uint256));
            }
        }
    }
}

/// @notice ERC-20 whose `transfer` returns false (never reverts) while `fail == true`, to exercise
///         SafeERC20.trySafeTransfer -> false -> pending credit. `transferFrom` always succeeds so
///         deposits/pulls work; only the push leg fails.
contract C_FalseReturningERC20 is MockERC20 {
    bool public fail = true;

    constructor() MockERC20("False USD", "fUSD", 6) {}

    function setFail(bool v) external {
        fail = v;
    }

    function transfer(address to, uint256 value) public override returns (bool) {
        if (fail) return false; // trySafeTransfer observes false and does NOT revert
        return super.transfer(to, value);
    }
}

/// @notice Attacker that, when armed, reenters claimPending() once on the inbound native push, records
///         the inner-revert selector, then returns so the outer push completes (the test asserts the
///         guard fired and there was no double-pay). While disarmed it reverts so a release push fails
///         and parks the proceeds as a pending credit.
contract C_ReentrantClaimer {
    address private auction;
    bool private armed;
    bool private entered;
    bytes4 public lastReentryError;

    function arm(address a, bool on) external {
        auction = a;
        armed = on;
    }

    receive() external payable {
        if (!armed) {
            revert("reject"); // disarmed: fail the push so proceeds are parked to pending
        }
        if (entered) return; // reenter only once
        entered = true;
        // Reenter the same nonReentrant function: the guard must reject this inner call.
        (bool ok, bytes memory ret) = auction.call(abi.encodeWithSignature("claimPending()"));
        if (!ok && ret.length >= 4) {
            lastReentryError = bytes4(ret);
        }
        // Return normally so the outer gas-capped push succeeds (single payout).
    }
}

/// @notice Attacker that reenters withdrawDeposit() once on the inbound native push, records the
///         inner-revert selector, then returns so the outer withdraw completes (the guard blocks the
///         inner call, no double-withdraw). It also records its own withdrawableFree(lotId, self)
///         mid-push (a staticcall) to prove CEI: a correct withdrawDeposit debits free before the
///         external push, so the recorded value must be 0.
contract C_ReentrantWithdrawer {
    address private auction;
    uint256 private lotId;
    uint256 private amount;
    bool private entered;
    bytes4 public lastReentryError;
    uint256 public freeDuringPush; // withdrawableFree(lotId, self) observed mid-push (CEI: must be 0)

    function arm(address a, uint256 lot, uint256 amt) external {
        auction = a;
        lotId = lot;
        amount = amt;
    }

    receive() external payable {
        if (entered) return;
        entered = true;
        // Read our own free mid-push: CEI requires it already debited before this external call.
        (bool okv, bytes memory rv) =
            auction.staticcall(abi.encodeWithSignature("withdrawableFree(uint256,address)", lotId, address(this)));
        if (okv && rv.length == 32) {
            freeDuringPush = abi.decode(rv, (uint256));
        }
        // Reenter the same nonReentrant function: the guard must reject it.
        (bool ok, bytes memory ret) =
            auction.call(abi.encodeWithSignature("withdrawDeposit(uint256,uint256)", lotId, amount));
        if (!ok && ret.length >= 4) {
            lastReentryError = bytes4(ret);
        }
        // Return normally so the outer push succeeds (single payout).
    }
}

/// @notice Malicious SELLER-receiver for the escrow-MOVING reentrancy tests. Installed via the openLot
///         seller arg, it receives the _release proceeds push and reenters a configured cross-function
///         escrow exit once (e.g. releaseAfterWindow while the outer call is confirmReceipt), records the
///         inner-revert selector, then returns (accepting the value) so the outer push completes and
///         escrow leaves exactly once. Accepting the value keeps the outer _release on its happy branch
///         so "escrow leaves exactly once" is the unconfounded subject.
contract C_ReentrantSeller {
    address private auction;
    bytes private reentryCall; // ABI-encoded cross-function call to attempt once on the inbound push
    bool private entered;
    bytes4 public lastReentryError;

    function arm(address a, bytes calldata call_) external {
        auction = a;
        reentryCall = call_;
    }

    receive() external payable {
        if (entered) return; // reenter only once
        entered = true;
        // Reenter a different fund-exit function: the nonReentrant guard must reject this inner call.
        (bool ok, bytes memory ret) = auction.call(reentryCall);
        if (!ok && ret.length >= 4) {
            lastReentryError = bytes4(ret);
        }
        // Return normally so the outer _release push succeeds (escrow exits exactly once).
    }
}

/// @notice Malicious ERC-1271 BUYER for the buyer-side escrow-MOVING reentrancy test. It doubles as the
///         winning bid principal: isValidSignature returns the magic value iff the ECDSA signature
///         recovers to the configured owner (the bidder1Key address), so the bid authorizes through
///         SignatureChecker's ERC-1271 branch. On the inbound _refund push (reclaimUndelivered) it
///         reenters a configured escrow exit (withdrawRefund) once, records the guard revert, then
///         returns (accepting the refund) so the outer refund completes and escrow leaves exactly once.
contract C_ReentrantBuyer is IERC1271 {
    using ECDSA for bytes32;

    address private immutable _owner; // the EOA address whose key signs the bid envelope (bidder1)
    address private auction;
    bytes private reentryCall;
    bool private entered;
    bytes4 public lastReentryError;

    /// @param owner_ the authorized ERC-1271 signer address (the bidder1 EOA derived from bidder1Key);
    ///        the contract accepts any signature that ECDSA-recovers to it.
    constructor(address owner_) {
        _owner = owner_;
    }

    function arm(address a, bytes calldata call_) external {
        auction = a;
        reentryCall = call_;
    }

    /// @dev ERC-1271: accept iff the ECDSA signature recovers to the authorized owner (bidder1).
    function isValidSignature(bytes32 hash, bytes calldata signature) external view override returns (bytes4) {
        address recovered = hash.recover(signature);
        if (recovered != address(0) && recovered == _owner) {
            return IERC1271.isValidSignature.selector; // 0x1626ba7e
        }
        return 0xffffffff;
    }

    receive() external payable {
        if (entered) return;
        entered = true;
        // Reenter an escrow-exit (withdrawRefund): the nonReentrant guard must reject this inner call.
        (bool ok, bytes memory ret) = auction.call(reentryCall);
        if (!ok && ret.length >= 4) {
            lastReentryError = bytes4(ret);
        }
        // Return normally so the outer refund push succeeds (escrow refunds exactly once).
    }
}
