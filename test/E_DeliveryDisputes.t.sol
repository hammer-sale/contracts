// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// End-to-end tests for the delivery + dispute lifecycle of a finalized lot: markDelivered,
// confirmReceipt, releaseAfterWindow, reclaimUndelivered, openDispute, resolveDispute.
//
// Behavior under test:
//   - markDelivered (AwaitingDelivery -> Delivered): stores the proof hash, pays nothing.
//   - confirmReceipt / releaseAfterWindow (Delivered -> Released/Settled): seller gets escrow minus
//     fee, feeRecipient gets the fee; releaseAfterWindow is permissionless once the dispute window
//     has elapsed.
//   - reclaimUndelivered (AwaitingDelivery -> Refunded): full escrow back to the buyer, no fee, once
//     the seller-deliver window has elapsed.
//   - openDispute (buyer or seller, from AwaitingDelivery|Delivered -> Disputed): pulls a separate
//     dispute bond and freezes the escrow.
//   - resolveDispute (arbiter only): routes escrow per Resolution and the bond to the winning party,
//     across all four opener x resolution combos; the bond is a separate pool, never escrowAmount.
//   - actor/access gates, state guards, and timing boundaries on every entrypoint.
//   - the bid-integrity gate: an open bonded integrity dispute (Class B) blocks every seller-paying
//     exit (BidIntegrityDisputeIsOpen) but never blocks refund/reclaim; a self-proving over-ceiling
//     challenge (Class A) never blocks release; clearing the gate re-enables release.
//   - fee math: fee == floor(amount*feeBps/10_000), proceeds == amount - fee, the truncation dust
//     goes to the seller; a zero feeBps makes no fee transfer.
//   - delivery entrypoints run while paused (none are whenNotPaused, so a pause cannot strand
//     in-flight escrow).
//   - timing anchors on the frozen awaitingAt/deliveredAt, never the soft-close-slidable endsAt.
//
// Reentrancy / no double-pay: the fund-paying terminals are nonReentrant and follow
// checks-effects-interactions (escrow zeroed + state flipped before any external push), so a
// reentrant counterparty re-entering from receive() has its nested call rejected
// (ReentrancyGuardReentrantCall) while the outer terminal pays out exactly once. openDispute's bond
// pull uses the bubbling SafeERC20.safeTransferFrom, so a hostile token whose transferFrom re-enters
// propagates the guard revert and reverts the whole openDispute. A dispute-bond winner that cannot
// accept its push is credited to pendingWithdrawals and the resolution still completes; the parked
// funds are recoverable via claimPending.
//
// Negative cases pin a specific error selector, never a bare expectRevert.

import {HammerBase} from "./HammerBase.t.sol";

import {SessionAuction} from "../src/SessionAuction.sol";
import {Clones} from "@openzeppelin/contracts/proxy/Clones.sol";
import {ISessionAuction} from "../src/interfaces/ISessionAuction.sol";
import {IFlagRegistry} from "../src/interfaces/IFlagRegistry.sol";
import {IPaddleRegistry} from "../src/interfaces/IPaddleRegistry.sol";
import {MockERC20} from "./mocks/MockERC20.sol";
import {
    Ceiling,
    AttestationQuote,
    NextCleanCandidate,
    InitConfig,
    Lot,
    LotPhase,
    DeliveryState,
    Resolution,
    CEILING_TYPEHASH
} from "../src/types/HammerTypes.sol";

import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";
import {ReentrancyGuardTransient} from "@openzeppelin/contracts/utils/ReentrancyGuardTransient.sol";
import {IERC1271} from "@openzeppelin/contracts/interfaces/IERC1271.sol";
import {ECDSA} from "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";

// Test-only adversarial fixtures. E_-prefixed names avoid collision with fixtures in sibling test
// files.

/// @dev A buyer/seller that re-enters the permissionless nonReentrant `releaseAfterWindow` from its
///      receive() when paid by a gas-capped push. It makes one re-entrant call and records the 4-byte
///      revert selector without reverting itself, so the outer push succeeds and the recipient is paid
///      exactly once; a nonzero recorded selector proves the nested call reverted. The body is minimal
///      so it fits a value-transfer gas stipend. The transient nonReentrant guard is contract-global,
///      so the nested error is ReentrancyGuardReentrantCall regardless of which terminal the outer
///      call is.
contract E_ReentrantParty is IERC1271 {
    using ECDSA for bytes32;

    SessionAuction private auction;
    uint256 private lotId;
    bytes4 public reentrySelector; // nonzero == the nested call reverted with this selector
    address private immutable _owner; // EOA whose key signs the bid envelope when this contract bids

    /// @param owner_ the authorized ERC-1271 signer (the EOA whose key signs the ceiling envelope when
    ///        THIS contract is the bid principal). Irrelevant (may be address(0)) when the fixture is
    ///        used purely as a seller.
    constructor(address owner_) {
        _owner = owner_;
    }

    /// @param a       the auction clone to re-enter
    /// @param lotId_  the lot to call releaseAfterWindow(lotId_) on
    function arm(SessionAuction a, uint256 lotId_) external {
        auction = a;
        lotId = lotId_;
    }

    /// @dev ERC-1271: accept iff the ECDSA signature recovers to the authorized owner, so this contract
    ///      can be the recorded bid principal (placeBid validates the ceiling envelope through
    ///      SignatureChecker, which routes a contract principal here).
    function isValidSignature(bytes32 hash, bytes calldata signature) external view override returns (bytes4) {
        address recovered = hash.recover(signature);
        if (recovered != address(0) && recovered == _owner) {
            return IERC1271.isValidSignature.selector; // 0x1626ba7e
        }
        return 0xffffffff;
    }

    receive() external payable {
        SessionAuction a = auction;

        if (address(a) == address(0)) return; // not armed

        // Re-enter on each push from the outer terminal. The nested releaseAfterWindow reverts at the
        // shared nonReentrant guard (it pushes nothing, so it cannot re-trigger this receive); a second
        // outer push (e.g. the bond leg after the proceeds leg) records the same selector again.
        (bool ok, bytes memory ret) =
            address(a).call(abi.encodeWithSelector(ISessionAuction.releaseAfterWindow.selector, lotId));

        if (!ok && ret.length >= 4) {
            reentrySelector = bytes4(ret);
        }

        // Do not revert: let the outer gas-capped push succeed so the terminal pays out exactly once.
    }
}

/// @dev A native receiver that reverts on any plain-value transfer while `reject` is true. As a
///      hostile dispute-bond winner the gas-capped bond/escrow push fails and falls back to a
///      pendingWithdrawals credit. Toggle `reject` off so a later claimPending pulls the parked amount.
contract E_RejectingReceiver {
    bool public reject = true;

    function setReject(bool v) external {
        reject = v;
    }

    receive() external payable {
        if (reject) revert("E_reject");
    }
}

/// @dev An ERC-20 whose `transfer` returns false (never reverts) while `fail` is true, exercising the
///      trySafeTransfer -> false -> pendingWithdrawals credit fallback for the ERC-20 dispute-bond
///      push. `transferFrom` always works (deposits and the bond pull succeed); only the push leg
///      fails until toggled.
contract E_FalseReturningERC20 is MockERC20 {
    bool public fail = true;

    constructor() MockERC20("E False USD", "efUSD", 6) {}

    function setFail(bool v) external {
        fail = v;
    }

    function transfer(address to, uint256 value) public override returns (bool) {
        if (fail) return false; // trySafeTransfer observes the false return and does NOT revert
        return super.transfer(to, value);
    }
}

/// @dev An ERC-20 whose `transferFrom` (the bond-pull leg of openDispute) re-enters a nonReentrant
///      delivery function while armed. The pull uses SafeERC20.safeTransferFrom, which bubbles the
///      callee revert, so the nested ReentrancyGuardReentrantCall bubbles out and reverts the outer
///      openDispute.
contract E_ReentrantPullERC20 is MockERC20 {
    SessionAuction private auction;
    bytes private reentryCalldata;
    bool private armed;

    constructor() MockERC20("E Reentrant USD", "erUSD", 6) {}

    function arm(SessionAuction a, bytes calldata callData) external {
        auction = a;
        reentryCalldata = callData;
        armed = true;
    }

    function transferFrom(address from, address to, uint256 value) public override returns (bool) {
        if (armed) {
            armed = false;

            // Re-enter a nonReentrant delivery function; the bubbling safeTransferFrom propagates the
            // revert.
            (bool ok, bytes memory ret) = address(auction).call(reentryCalldata);

            if (!ok) {
                assembly {
                    revert(add(ret, 0x20), mload(ret))
                }
            }
        }

        return super.transferFrom(from, to, value);
    }
}

contract DeliveryDisputesTest is HammerBase {
    uint256 internal constant LOT_ID = 1;

    // Winner escrow on the native rail. Chosen so escrow*FEE_BPS divides 10_000 exactly, giving a clean
    // happy-path fee/proceeds split; the dust tests use their own amounts.
    uint128 internal constant ESCROW_E = 100 ether;

    // Committed ceiling for the over-ceiling-winner case: strictly below the bid amount (ESCROW_E) so a
    // later challengeOverCeiling both opens (the commit matches) and clears the amount > maxBid check
    // that makes the over-ceiling claim valid.
    uint128 internal constant E_OVER_MAXBID = ESCROW_E - 1 ether; // committed cap < ESCROW_E (over-ceiling)
    bytes32 internal constant E_OVER_SALT = bytes32("salt"); // salt the over-ceiling commit opens with

    bytes32 internal constant PROOF_HASH = keccak256("DELIVERY_PROOF");
    bytes32 internal constant PHOTO_HASH = keccak256("RECEIPT_PHOTO");
    bytes32 internal constant CLAIM_REF = keccak256("DISPUTE_CLAIM");
    bytes32 internal constant ARB_PHOTO = keccak256("ARBITER_EVIDENCE");
    string internal constant DELIVERY_CID = "ipfs://delivery";
    string internal constant PHOTO_CID = "ipfs://photo";

    // Void-path KYC paddles (nonzero == registered): a flagged offender as provisional top vs a clean
    // candidate promoted into delivery (used only by _driveToAwaitingViaVoid).
    uint16 internal constant E_PADDLE_OFFENDER = 711; // flagged provisional top
    uint16 internal constant E_PADDLE_CLEAN = 611; // clean next-best, promoted winner

    // Bidder signing keys bound to the named HammerBase addresses. makeAddrAndKey is address-stable
    // (same label -> same address) and returns the key, so re-deriving here binds a key to the same
    // address. placeBid validates the ceiling envelope through SignatureChecker against `principal`, so
    // each EOA principal needs a real ECDSA signature over the clone domain (a fake sig reverts
    // BadSignature).
    uint256 internal bidder1Key;
    uint256 internal bidder2Key;

    // EIP-712 domain constants for a clone (it is constructed as EIP712("Hammer","1"), with the domain
    // separator's verifyingContract resolving to the clone address).
    bytes32 internal constant EIP712_TYPE_HASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 internal constant HASHED_NAME = keccak256(bytes("Hammer"));
    bytes32 internal constant HASHED_VERSION = keccak256(bytes("1"));

    /// @dev Run the base setUp, then re-derive the bidder signing keys against the same named addresses
    ///      HammerBase seeded (makeAddrAndKey is address-stable), so the ceiling envelopes the bid
    ///      helpers build carry a recoverable ECDSA signature.
    function setUp() public virtual override {
        super.setUp();
        (, bidder1Key) = makeAddrAndKey("bidder1");
        (, bidder2Key) = makeAddrAndKey("bidder2");
    }

    // Reverse-map for contract bid principals (e.g. the ERC-1271 reentrant buyer): maps the contract to
    // the key its isValidSignature accepts (its ERC-1271 owner). Populated by a driver at test time.
    mapping(address => uint256) private _contractSignerKey;
    mapping(address => bool) private _contractSignerSet;

    function _bindContractSigner(address contractPrincipal, uint256 ownerKey) private {
        _contractSignerKey[contractPrincipal] = ownerKey;
        _contractSignerSet[contractPrincipal] = true;
    }

    /// @dev The bound signing key for a bid principal (the two named EOAs and any registered ERC-1271
    ///      contract principal). placeBid validates the ceiling signature against `principal`, so each
    ///      must sign with the matching key. An unknown principal reverts (a test wiring error) rather
    ///      than signing with the wrong key and tripping BadSignature on-chain.
    function _signerKeyFor(address principal) private view returns (uint256) {
        if (_contractSignerSet[principal]) return _contractSignerKey[principal];
        if (principal == bidder1) return bidder1Key;
        if (principal == bidder2) return bidder2Key;
        revert("E: no signing key bound for principal");
    }

    /// @dev EIP-712 domain separator for `clone` (verifyingContract == the clone address).
    function _domainSeparator(address clone) private view returns (bytes32) {
        return keccak256(abi.encode(EIP712_TYPE_HASH, HASHED_NAME, HASHED_VERSION, block.chainid, clone));
    }

    /// @dev Sign the Ceiling over the clone domain so SignatureChecker recovers the principal. Matches
    ///      the on-chain hash preimage: CEILING_TYPEHASH over the eight Ceiling fields.
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

    // markDelivered (AwaitingDelivery -> Delivered): stores proofHash, sets deliveredAt, pays nothing,
    // escrow unchanged, emits Delivered. The chain does not verify the media itself.
    function test_MarkDelivered() public {
        _driveToAwaiting(address(0), ESCROW_E);

        uint256 balBefore = address(auction).balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Delivered(LOT_ID, PROOF_HASH, DELIVERY_CID);

        vm.prank(seller);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Delivered), "deliveryState Delivered");
        assertEq(uint8(lot.phase), uint8(LotPhase.Awaiting), "phase stays Awaiting");
        assertEq(lot.deliveryProofHash, PROOF_HASH, "proofHash stored");
        assertEq(uint256(lot.deliveredAt), block.timestamp, "deliveredAt == now");
        assertEq(uint256(lot.escrowAmount), ESCROW_E, "escrow unchanged");
        assertEq(address(auction).balance, balBefore, "no payout, contract balance unchanged");
    }

    // confirmReceipt (buyer only, Delivered -> Released): seller gets escrow minus fee, feeRecipient
    // gets the fee, escrow zeroed, phase Settled, proceeds + fee == escrow. Both rails.
    function test_ConfirmReceiptReleasesToSeller() public {
        _confirmReceiptReleasesToSeller(address(0));
        _resetAndConfirmReceiptToken();
    }

    function _resetAndConfirmReceiptToken() private {
        setUp();
        _confirmReceiptReleasesToSeller(address(token));
    }

    function _confirmReceiptReleasesToSeller(address payToken) private {
        _driveToDelivered(payToken, ESCROW_E);

        uint256 fee = Math.mulDiv(ESCROW_E, FEE_BPS, 10_000);
        uint256 proceeds = ESCROW_E - fee;
        assertEq(proceeds + fee, ESCROW_E, "proceeds + fee == E");

        (uint256 sellerBefore, uint256 feeRecipBefore) = _balances(payToken, seller, houseFeeRecipient);
        uint256 escrowBefore = _heldEscrow(payToken);

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Confirmed(LOT_ID, PHOTO_HASH, PHOTO_CID);
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);

        vm.prank(bidder1);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), 0, "escrow zeroed");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Released), "deliveryState Released");
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "phase Settled");

        (uint256 sellerAfter, uint256 feeRecipAfter) = _balances(payToken, seller, houseFeeRecipient);
        assertEq(sellerAfter - sellerBefore, proceeds, "seller paid proceeds");
        assertEq(feeRecipAfter - feeRecipBefore, fee, "feeRecipient paid fee");
        // fund conservation: escrow held leaves the contract in full as proceeds + fee.
        assertEq(escrowBefore, _heldEscrow(payToken) + proceeds + fee, "escrow conserved out");
    }

    // releaseAfterWindow (permissionless, Delivered -> Released) once now >= deliveredAt +
    // disputeWindowSec: emits DeliveryAutoReleased then Released. Stops a buyer holding escrow hostage
    // by never confirming. Both rails.
    function test_ReleaseAfterWindow() public {
        _releaseAfterWindow(address(0));
        setUp();
        _releaseAfterWindow(address(token));
    }

    function _releaseAfterWindow(address payToken) private {
        _driveToDelivered(payToken, ESCROW_E);

        uint256 deliveredAt = uint256(auction.getLot(LOT_ID).deliveredAt);
        uint256 fee = Math.mulDiv(ESCROW_E, FEE_BPS, 10_000);
        uint256 proceeds = ESCROW_E - fee;

        (uint256 sellerBefore, uint256 feeRecipBefore) = _balances(payToken, seller, houseFeeRecipient);

        vm.warp(deliveredAt + DISPUTE_WINDOW_SEC); // exactly at the boundary

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.DeliveryAutoReleased(LOT_ID, seller);
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);

        vm.prank(bidder3); // permissionless keeper (neither buyer nor seller)
        auction.releaseAfterWindow(LOT_ID);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), 0, "escrow zeroed");
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "phase Settled");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Released), "deliveryState Released");

        (uint256 sellerAfter, uint256 feeRecipAfter) = _balances(payToken, seller, houseFeeRecipient);
        assertEq(sellerAfter - sellerBefore, proceeds, "seller paid proceeds");
        assertEq(feeRecipAfter - feeRecipBefore, fee, "feeRecipient paid fee");
    }

    // releaseAfterWindow boundary: DisputeWindowNotElapsed one second early; WrongDeliveryState if not
    // Delivered. Escrow untouched in both cases.
    function test_RevertWhen_ReleaseBeforeWindow() public {
        _driveToDelivered(address(0), ESCROW_E);
        uint256 deliveredAt = uint256(auction.getLot(LOT_ID).deliveredAt);

        vm.warp(deliveredAt + DISPUTE_WINDOW_SEC - 1); // one second before the window elapses

        vm.expectRevert(ISessionAuction.DisputeWindowNotElapsed.selector);
        auction.releaseAfterWindow(LOT_ID);

        assertEq(uint256(auction.getLot(LOT_ID).escrowAmount), ESCROW_E, "escrow untouched");
    }

    function test_RevertWhen_ReleaseWrongState() public {
        // AwaitingDelivery: not yet Delivered -> WrongDeliveryState, even after a long wait.
        _driveToAwaiting(address(0), ESCROW_E);
        vm.warp(block.timestamp + 365 days);

        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.releaseAfterWindow(LOT_ID);

        assertEq(uint256(auction.getLot(LOT_ID).escrowAmount), ESCROW_E, "escrow untouched");
    }

    // A Disputed lot is frozen, so releaseAfterWindow reverts WrongDeliveryState even past
    // deliveredAt + disputeWindowSec (the only way out is resolveDispute).
    function test_RevertWhen_ReleaseFromDisputed() public {
        // open from Delivered so a deliveredAt anchor exists; warp past the would-be auto-release window.
        _driveToDisputedFrom(address(0), ESCROW_E, seller, true /* viaDelivered */);
        uint256 deliveredAt = uint256(auction.getLot(LOT_ID).deliveredAt);
        vm.warp(deliveredAt + DISPUTE_WINDOW_SEC + 1 days);

        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.releaseAfterWindow(LOT_ID);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Disputed), "stays Disputed (frozen)");
        assertEq(uint256(lot.escrowAmount), ESCROW_E, "escrow frozen, untouched");
        assertEq(uint256(lot.disputeBond), uint256(DISPUTE_BOND_AMT), "bond still held");
    }

    // reclaimUndelivered (buyer only, AwaitingDelivery -> Refunded) once now >= awaitingAt +
    // sellerDeliverSec: full escrow back to the buyer, no fee, phase Refunded. Both rails.
    function test_ReclaimUndelivered() public {
        _reclaimUndelivered(address(0));
        setUp();
        _reclaimUndelivered(address(token));
    }

    function _reclaimUndelivered(address payToken) private {
        _driveToAwaiting(payToken, ESCROW_E);

        uint256 awaitingAt = uint256(auction.getLot(LOT_ID).awaitingAt);
        uint256 buyerBefore = _bal(payToken, bidder1);

        vm.warp(awaitingAt + SELLER_DELIVER_SEC); // exactly at the boundary

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.ReclaimedUndelivered(LOT_ID, bidder1, ESCROW_E);
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Refunded(LOT_ID, bidder1, ESCROW_E);

        vm.prank(bidder1);
        auction.reclaimUndelivered(LOT_ID);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), 0, "escrow zeroed");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Refunded), "deliveryState Refunded");
        assertEq(uint8(lot.phase), uint8(LotPhase.Refunded), "phase Refunded");
        assertEq(_bal(payToken, bidder1) - buyerBefore, ESCROW_E, "buyer refunded FULL escrow, no fee");
    }

    // reclaimUndelivered boundary: DeliveryWindowNotElapsed before the window; WrongDeliveryState if
    // not AwaitingDelivery. Escrow untouched in both cases.
    function test_RevertWhen_ReclaimBeforeWindow() public {
        _driveToAwaiting(address(0), ESCROW_E);
        uint256 awaitingAt = uint256(auction.getLot(LOT_ID).awaitingAt);

        vm.warp(awaitingAt + SELLER_DELIVER_SEC - 1); // one second before the window elapses

        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.DeliveryWindowNotElapsed.selector);
        auction.reclaimUndelivered(LOT_ID);

        assertEq(uint256(auction.getLot(LOT_ID).escrowAmount), ESCROW_E, "escrow untouched");
    }

    function test_RevertWhen_ReclaimWrongState() public {
        // Delivered: no longer AwaitingDelivery -> WrongDeliveryState even past every timeout.
        _driveToDelivered(address(0), ESCROW_E);
        vm.warp(block.timestamp + 365 days);

        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.reclaimUndelivered(LOT_ID);

        assertEq(uint256(auction.getLot(LOT_ID).escrowAmount), ESCROW_E, "escrow untouched");
    }

    // A buyer who already opened a dispute must not also reclaim the escrow. From Disputed (opened by
    // the buyer here), reclaimUndelivered reverts WrongDeliveryState even past awaitingAt +
    // sellerDeliverSec.
    function test_RevertWhen_ReclaimFromDisputed() public {
        // buyer (bidder1) opens the dispute from AwaitingDelivery, then tries to also reclaim.
        _driveToDisputed(address(0), ESCROW_E, bidder1);
        uint256 awaitingAt = uint256(auction.getLot(LOT_ID).awaitingAt);
        vm.warp(awaitingAt + SELLER_DELIVER_SEC + 1 days);

        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.reclaimUndelivered(LOT_ID);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Disputed), "stays Disputed (frozen)");
        assertEq(uint256(lot.escrowAmount), ESCROW_E, "escrow frozen, untouched");
        assertEq(uint256(lot.disputeBond), uint256(DISPUTE_BOND_AMT), "bond still held");
    }

    // A late markDelivered still wins the race if it lands first. markDelivered has no upper time bound
    // (its only precondition is phase Awaiting && deliveryState AwaitingDelivery), so the seller can
    // mark delivered even at/past awaitingAt + sellerDeliverSec (the instant reclaim first becomes
    // legal), as long as the buyer has not reclaimed. Once it lands, the buyer's reclaimUndelivered
    // reverts WrongDeliveryState (the lot left the reclaimable state, the clock no longer matters).
    function test_MarkDeliveredWinsRacePastReclaimWindow() public {
        _driveToAwaiting(address(0), ESCROW_E);

        uint256 awaitingAt = uint256(auction.getLot(LOT_ID).awaitingAt);

        // the exact reclaim boundary: reclaim's `>=` guard is satisfied here, yet markDelivered is still
        // legal (no upper time bound).
        vm.warp(awaitingAt + SELLER_DELIVER_SEC);

        uint256 heldBefore = address(auction).balance;

        // seller lands markDelivered first, at the reclaim boundary: it succeeds and emits Delivered.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Delivered(LOT_ID, PROOF_HASH, DELIVERY_CID);

        vm.prank(seller);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Delivered), "late-but-first markDelivered wins: Delivered");
        assertEq(uint8(lot.phase), uint8(LotPhase.Awaiting), "phase stays Awaiting (no terminal yet)");
        assertEq(lot.deliveryProofHash, PROOF_HASH, "proofHash stored at the boundary");
        assertEq(uint256(lot.deliveredAt), block.timestamp, "deliveredAt == now (the boundary instant)");
        assertEq(uint256(lot.escrowAmount), ESCROW_E, "escrow unchanged (markDelivered pays nothing)");
        assertEq(address(auction).balance, heldBefore, "no payout: contract balance unchanged");

        // the lot left AwaitingDelivery, so the buyer's reclaim reverts WrongDeliveryState (the window is
        // elapsed but the state is wrong), even at/past the reclaim boundary.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.reclaimUndelivered(LOT_ID);

        // well past the boundary the seller's win still holds (the state, not the clock, blocks reclaim).
        vm.warp(awaitingAt + SELLER_DELIVER_SEC + 365 days);
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.reclaimUndelivered(LOT_ID);

        Lot memory post = auction.getLot(LOT_ID);
        assertEq(uint8(post.deliveryState), uint8(DeliveryState.Delivered), "still Delivered (reclaim never fired)");
        assertEq(uint256(post.escrowAmount), ESCROW_E, "escrow still held in full");
    }

    // openDispute (buyer or seller, from AwaitingDelivery|Delivered -> Disputed): pulls the dispute
    // bond, stores opener/bond/ref (pulled == stored == emitted), and freezes the escrow. Both rails;
    // the bond pool is separate from the escrow.
    function test_OpenDisputeFreezesEscrow() public {
        // buyer opens from AwaitingDelivery (native rail).
        _openDisputeFreezesEscrow(address(0), bidder1, true);
        // seller opens from Delivered (ERC-20 rail).
        setUp();
        _openDisputeFreezesEscrow(address(token), seller, false);
    }

    function _openDisputeFreezesEscrow(address payToken, address opener, bool fromAwaiting) private {
        if (fromAwaiting) {
            _driveToAwaiting(payToken, ESCROW_E);
        } else {
            _driveToDelivered(payToken, ESCROW_E);
        }

        // Fund the opener for the bond on the chosen rail, then snapshot after the top-up so the delta
        // below is purely the bond pull (not offset by the funding deal/mint). Inlined (not via
        // _openDisputeAs) so the fund-then-snapshot-then-pull ordering is observable.
        if (payToken == address(0)) {
            vm.deal(opener, opener.balance + uint256(DISPUTE_BOND_AMT));
        } else {
            token.mint(opener, uint256(DISPUTE_BOND_AMT));
            vm.prank(opener);
            token.approve(address(auction), DISPUTE_BOND_AMT);
        }

        uint256 escrowBefore = _heldEscrow(payToken);
        uint256 openerBefore = _bal(payToken, opener); // post-top-up: the exact balance the bond leaves

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.DisputeOpened(LOT_ID, opener, DISPUTE_BOND_AMT, CLAIM_REF);

        if (payToken == address(0)) {
            vm.prank(opener);
            auction.openDispute{value: DISPUTE_BOND_AMT}(LOT_ID, CLAIM_REF);
        } else {
            vm.prank(opener);
            auction.openDispute(LOT_ID, CLAIM_REF); // ERC-20 bond: msg.value == 0
        }

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Disputed), "deliveryState Disputed");
        assertEq(lot.disputeOpener, opener, "disputeOpener stored");
        assertEq(uint256(lot.disputeBond), uint256(DISPUTE_BOND_AMT), "disputeBond stored == pulled");
        assertEq(lot.disputeRef, CLAIM_REF, "disputeRef stored");
        // escrow frozen: escrowAmount unchanged, only the separate bond pool moved in.
        assertEq(uint256(lot.escrowAmount), ESCROW_E, "escrow frozen, untouched");
        assertEq(_heldEscrow(payToken), escrowBefore + DISPUTE_BOND_AMT, "only bond pulled in");
        // the opener's own balance drops by exactly the bond (it really left the opener, not merely the
        // contract's held balance rising). Both rails.
        assertEq(openerBefore - _bal(payToken, opener), uint256(DISPUTE_BOND_AMT), "bond pulled FROM the opener");
    }

    // The Disputed freeze: from Disputed the only outward edge is resolveDispute; every other exit
    // (markDelivered, confirmReceipt, releaseAfterWindow, reclaimUndelivered) reverts WrongDeliveryState,
    // even after the relevant timeout, and no wei moves (escrow and bond stay held). Driven via Delivered
    // so a deliveredAt anchor exists.
    function test_DisputedStateFreezesAllNonResolveExits() public {
        // open from Delivered (seller marks first, buyer opens) so the lot carries both a deliveredAt and
        // an awaitingAt anchor; the buyer is the opener so the seller is still a legitimate party.
        _driveToDisputedFrom(address(0), ESCROW_E, bidder1, true /* viaDelivered */);

        Lot memory pre = auction.getLot(LOT_ID);
        assertEq(uint8(pre.deliveryState), uint8(DeliveryState.Disputed), "precondition: Disputed");
        uint256 awaitingAt = uint256(pre.awaitingAt);
        uint256 deliveredAt = uint256(pre.deliveredAt);
        uint256 heldBefore = _heldEscrow(address(0)); // escrow E + bond, both native

        // (1) markDelivered (seller): the state guard fires (Disputed, not AwaitingDelivery).
        vm.prank(seller);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);

        // (2) confirmReceipt (buyer): legal only from Delivered, not Disputed.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        // (3) releaseAfterWindow (permissionless): even past the auto-release window, the Disputed state
        //     guard precedes the window check and blocks the auto-release.
        vm.warp(deliveredAt + DISPUTE_WINDOW_SEC + 1 days);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.releaseAfterWindow(LOT_ID);

        // (4) reclaimUndelivered (buyer): even past the seller-deliver window, the Disputed state guard
        //     blocks the no-strand refund.
        vm.warp(awaitingAt + SELLER_DELIVER_SEC + 1 days);
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.reclaimUndelivered(LOT_ID);

        // the freeze held: no wei moved out of either pool, deliveryState is still Disputed.
        Lot memory post = auction.getLot(LOT_ID);
        assertEq(uint8(post.deliveryState), uint8(DeliveryState.Disputed), "freeze: still Disputed");
        assertEq(uint8(post.phase), uint8(LotPhase.Awaiting), "freeze: phase still Awaiting (no terminal)");
        assertEq(uint256(post.escrowAmount), ESCROW_E, "freeze: escrow still held in full");
        assertEq(uint256(post.disputeBond), uint256(DISPUTE_BOND_AMT), "freeze: bond still held in full");
        assertEq(_heldEscrow(address(0)), heldBefore, "freeze: contract balance unchanged (no payout)");
        assertEq(
            _heldEscrow(address(0)),
            uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT),
            "freeze: contract still holds escrow + bond"
        );
    }

    // openDispute reverts: non-party Unauthorized; double-open AlreadyDisputed; Delivered after the
    // window DisputeWindowElapsed; native msg.value mismatch (under and over) WrongBond; ERC-20 with a
    // nonzero msg.value WrongBond. No bond pulled in any case.
    function test_RevertWhen_OpenDisputeNotParty() public {
        _driveToAwaiting(address(0), ESCROW_E);

        // bidder2 is neither the buyer (bidder1) nor the seller.
        vm.deal(bidder2, INITIAL_ETH);
        vm.prank(bidder2);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.openDispute{value: DISPUTE_BOND_AMT}(LOT_ID, CLAIM_REF);

        assertEq(uint8(auction.getLot(LOT_ID).deliveryState), uint8(DeliveryState.AwaitingDelivery), "no transition");
    }

    function test_RevertWhen_DoubleDispute() public {
        _driveToAwaiting(address(0), ESCROW_E);

        // first open succeeds (buyer bidder1 is the opener); a second must revert AlreadyDisputed.
        _openDisputeAs(address(0), bidder1, CLAIM_REF);

        // The second opener is the seller (the other legitimate party). Fund it, snapshot, and assert the
        // failed second open pulls nothing and leaves the original dispute intact (opener not overwritten,
        // bond not doubled).
        vm.deal(seller, seller.balance + uint256(DISPUTE_BOND_AMT));
        uint256 sellerBefore = seller.balance;

        vm.prank(seller);
        vm.expectRevert(ISessionAuction.AlreadyDisputed.selector);
        auction.openDispute{value: DISPUTE_BOND_AMT}(LOT_ID, CLAIM_REF);

        // the original dispute (opener bidder1) is untouched: opener not overwritten, a single bond held,
        // ref/escrow preserved, and the seller paid no second bond.
        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Disputed), "double-open: still Disputed");
        assertEq(lot.disputeOpener, bidder1, "double-open: original opener NOT overwritten by the seller");
        assertEq(uint256(lot.disputeBond), uint256(DISPUTE_BOND_AMT), "double-open: single bond held, not doubled");
        assertEq(lot.disputeRef, CLAIM_REF, "double-open: original claimRef preserved");
        assertEq(uint256(lot.escrowAmount), ESCROW_E, "double-open: escrow frozen, untouched");
        // exactly ONE bond held alongside the escrow (the second bond was never pulled).
        assertEq(
            _heldEscrow(address(0)),
            uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT),
            "double-open: contract holds escrow + exactly ONE bond"
        );
        assertEq(seller.balance, sellerBefore, "double-open: failed second open pulled no bond from the seller");
    }

    function test_RevertWhen_DisputeAfterWindow() public {
        _driveToDelivered(address(0), ESCROW_E);
        uint256 deliveredAt = uint256(auction.getLot(LOT_ID).deliveredAt);

        // auto-release window already lapsed -> a dispute can no longer be opened on a Delivered lot.
        vm.warp(deliveredAt + DISPUTE_WINDOW_SEC);

        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.DisputeWindowElapsed.selector);
        auction.openDispute{value: DISPUTE_BOND_AMT}(LOT_ID, CLAIM_REF);

        assertEq(uint8(auction.getLot(LOT_ID).deliveryState), uint8(DeliveryState.Delivered), "no transition");
    }

    function test_RevertWhen_DisputeWrongBond() public {
        // native rail: msg.value != _disputeBondAmt reverts WrongBond, both under and over.
        _driveToAwaiting(address(0), ESCROW_E);

        // After each native revert (under, then over) the lot must not transition, no bond is stored, and
        // msg.value is fully returned. Snapshot the opener and the contract balance to prove it.
        uint256 contractBefore = address(auction).balance;
        uint256 bidderBefore = bidder1.balance;

        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongBond.selector);
        auction.openDispute{value: DISPUTE_BOND_AMT - 1}(LOT_ID, CLAIM_REF); // under

        {
            Lot memory underLot = auction.getLot(LOT_ID);
            assertEq(uint8(underLot.deliveryState), uint8(DeliveryState.AwaitingDelivery), "under: no transition");
            assertEq(uint256(underLot.disputeBond), 0, "under: no bond stored");
        }
        assertEq(address(auction).balance, contractBefore, "under: contract captured nothing on revert");
        assertEq(bidder1.balance, bidderBefore, "under: msg.value fully returned to opener");

        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongBond.selector);
        auction.openDispute{value: DISPUTE_BOND_AMT + 1}(LOT_ID, CLAIM_REF); // over

        {
            Lot memory overLot = auction.getLot(LOT_ID);
            assertEq(uint8(overLot.deliveryState), uint8(DeliveryState.AwaitingDelivery), "over: no transition");
            assertEq(uint256(overLot.disputeBond), 0, "over: no bond stored");
        }
        assertEq(address(auction).balance, contractBefore, "over: contract captured nothing on revert");
        assertEq(bidder1.balance, bidderBefore, "over: msg.value fully returned to opener");

        // ERC-20 rail: a nonzero msg.value alongside the token bond reverts WrongBond. Nothing is pulled
        // on either asset: the approved allowance is not consumed and the stray 1 wei of native msg.value
        // is not captured. Snapshot both rails after the approve to prove it.
        setUp();
        _driveToAwaiting(address(token), ESCROW_E);
        vm.prank(bidder1);
        token.approve(address(auction), DISPUTE_BOND_AMT);

        uint256 openerTokenBefore = token.balanceOf(bidder1);
        uint256 contractTokenBefore = token.balanceOf(address(auction));
        uint256 openerNativeBefore = bidder1.balance;
        uint256 contractNativeBefore = address(auction).balance;
        // the allowance is in place; the revert must leave it unspent.
        assertEq(token.allowance(bidder1, address(auction)), uint256(DISPUTE_BOND_AMT), "erc20: allowance armed pre-call");

        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongBond.selector);
        auction.openDispute{value: 1}(LOT_ID, CLAIM_REF);

        Lot memory ercLot = auction.getLot(LOT_ID);
        assertEq(uint8(ercLot.deliveryState), uint8(DeliveryState.AwaitingDelivery), "erc20: no transition");
        assertEq(uint256(ercLot.disputeBond), 0, "erc20: no bond stored");
        // the token bond was not pulled: opener balance, contract balance, and allowance all unchanged
        // (safeTransferFrom never ran before the msg.value assert).
        assertEq(token.balanceOf(bidder1), openerTokenBefore, "erc20: opener token balance unchanged (no bond pulled)");
        assertEq(token.balanceOf(address(auction)), contractTokenBefore, "erc20: contract token balance unchanged");
        assertEq(token.allowance(bidder1, address(auction)), uint256(DISPUTE_BOND_AMT), "erc20: allowance NOT consumed");
        // the stray 1 wei of native msg.value was fully returned (nothing captured on either rail).
        assertEq(bidder1.balance, openerNativeBefore, "erc20: native 1 wei fully returned to opener");
        assertEq(address(auction).balance, contractNativeBefore, "erc20: contract captured no native wei");
    }

    // openDispute is legal only from {AwaitingDelivery, Delivered}. A real party calling it from a
    // pre-finalize phase (Hammered + revealed, deliveryState == None) reverts WrongDeliveryState (the
    // state guard, not Unauthorized, since the caller is a party) and pulls no bond. The pre-finalize
    // counterpart of test_RevertWhen_OpenDisputeFromTerminalPhase.
    function test_RevertWhen_OpenDisputeBeforeFinalize() public {
        // Hammered + revealed + AC window closed, but finalizeWinner NOT called: deliveryState == None.
        _driveToHammeredRevealed(address(0), ESCROW_E);

        Lot memory pre = auction.getLot(LOT_ID);
        assertEq(uint8(pre.deliveryState), uint8(DeliveryState.None), "precondition: deliveryState None (pre-finalize)");
        assertEq(uint8(pre.phase), uint8(LotPhase.Hammered), "precondition: phase Hammered");

        uint256 heldBefore = address(auction).balance;

        // the seller is a real party (lot.seller), so the revert is the state guard, not Unauthorized.
        vm.deal(seller, seller.balance + uint256(DISPUTE_BOND_AMT));
        vm.prank(seller);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.openDispute{value: DISPUTE_BOND_AMT}(LOT_ID, CLAIM_REF);

        Lot memory post = auction.getLot(LOT_ID);
        assertEq(uint8(post.deliveryState), uint8(DeliveryState.None), "pre-finalize: no transition");
        assertEq(uint256(post.disputeBond), 0, "pre-finalize: no bond stored");
        assertEq(address(auction).balance, heldBefore, "pre-finalize: no bond pulled in");
    }

    // resolveDispute (arbiter only) routes escrow per Resolution and the bond always to the winning party
    // (bond zeroed before the push, per checks-effects-interactions), across all four opener x resolution
    // combos. The bond never touches escrowAmount (separate pool). Native + ERC-20.
    function test_ResolveDisputeBondToWinner() public {
        // ReleaseToSeller, opener == seller -> escrow to seller (minus fee), bond back to opener (seller).
        _resolveReleaseToSeller(address(0), seller, seller);
        // ReleaseToSeller, opener == buyer (loses) -> escrow to seller, bond forfeit to seller.
        setUp();
        _resolveReleaseToSeller(address(token), bidder1, seller);
        // RefundToBuyer, opener == buyer -> full escrow to buyer, bond back to opener (buyer).
        setUp();
        _resolveRefundToBuyer(address(0), bidder1, bidder1);
        // RefundToBuyer, opener == seller (loses) -> full escrow to buyer, bond forfeit to buyer.
        setUp();
        _resolveRefundToBuyer(address(token), seller, bidder1);
    }

    function _resolveReleaseToSeller(address payToken, address opener, address bondRecipient) private {
        _driveToDisputed(payToken, ESCROW_E, opener);

        uint256 fee = Math.mulDiv(ESCROW_E, FEE_BPS, 10_000);
        uint256 proceeds = ESCROW_E - fee;

        uint256 sellerBefore = _bal(payToken, seller);
        uint256 bondRecipBefore = _bal(payToken, bondRecipient);
        // no-strand: held == escrow + bond before resolution, both pools must leave in full.
        uint256 heldBefore = _heldEscrow(payToken);
        assertEq(heldBefore, uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT), "held == escrow + bond pre-resolve");

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.DisputeResolved(LOT_ID, Resolution.ReleaseToSeller, bondRecipient);

        vm.prank(arbiter);
        auction.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, ARB_PHOTO);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), 0, "escrow zeroed");
        assertEq(uint256(lot.disputeBond), 0, "bond zeroed (CEI)");
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "phase Settled");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Released), "deliveryState Released");

        if (bondRecipient == seller) {
            // seller receives both proceeds and the bond.
            assertEq(
                _bal(payToken, seller) - sellerBefore,
                proceeds + uint256(DISPUTE_BOND_AMT),
                "seller paid proceeds + bond"
            );
        } else {
            assertEq(_bal(payToken, seller) - sellerBefore, proceeds, "seller paid proceeds only");
            assertEq(_bal(payToken, bondRecipient) - bondRecipBefore, uint256(DISPUTE_BOND_AMT), "bond to winner");
        }
        // both pools left the contract: proceeds + fee == escrow, so held drops by exactly escrow + bond
        // to 0 (this clone holds only this lot's funds).
        assertEq(_heldEscrow(payToken), 0, "release: contract fully drained (escrow + bond), no strand");
        assertEq(
            heldBefore - _heldEscrow(payToken),
            uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT),
            "release: held dropped by exactly escrow + bond"
        );
    }

    function _resolveRefundToBuyer(address payToken, address opener, address bondRecipient) private {
        _driveToDisputed(payToken, ESCROW_E, opener);

        uint256 buyerBefore = _bal(payToken, bidder1);
        uint256 bondRecipBefore = _bal(payToken, bondRecipient);
        // no-strand: held == escrow + bond before resolution, both pools must leave in full.
        uint256 heldBefore = _heldEscrow(payToken);
        assertEq(heldBefore, uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT), "held == escrow + bond pre-resolve");

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Refunded(LOT_ID, bidder1, ESCROW_E);
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.DisputeResolved(LOT_ID, Resolution.RefundToBuyer, bondRecipient);

        vm.prank(arbiter);
        auction.resolveDispute(LOT_ID, Resolution.RefundToBuyer, ARB_PHOTO);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), 0, "escrow zeroed");
        assertEq(uint256(lot.disputeBond), 0, "bond zeroed (CEI)");
        assertEq(uint8(lot.phase), uint8(LotPhase.Refunded), "phase Refunded");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Refunded), "deliveryState Refunded");

        if (bondRecipient == bidder1) {
            // buyer receives both the full escrow and the bond.
            assertEq(
                _bal(payToken, bidder1) - buyerBefore,
                uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT),
                "buyer refunded escrow + bond"
            );
        } else {
            assertEq(_bal(payToken, bidder1) - buyerBefore, uint256(ESCROW_E), "buyer refunded escrow only");
            assertEq(_bal(payToken, bondRecipient) - bondRecipBefore, uint256(DISPUTE_BOND_AMT), "bond to winner");
        }
        // both pools left the contract: refund pays the full escrow (no fee), so held drops by exactly
        // escrow + bond to 0.
        assertEq(_heldEscrow(payToken), 0, "refund: contract fully drained (escrow + bond), no strand");
        assertEq(
            heldBefore - _heldEscrow(payToken),
            uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT),
            "refund: held dropped by exactly escrow + bond"
        );
    }

    // resolveDispute access + state guard: a non-arbiter reverts Unauthorized; it is legal only from
    // Disputed (else WrongDeliveryState).
    function test_RevertWhen_ResolveDisputeNotArbiter() public {
        _driveToDisputed(address(0), ESCROW_E, bidder1);

        // seller is a party but NOT the arbiter.
        vm.prank(seller);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, ARB_PHOTO);

        assertEq(uint8(auction.getLot(LOT_ID).deliveryState), uint8(DeliveryState.Disputed), "no transition");
    }

    function test_RevertWhen_ResolveDisputeWrongState() public {
        // arbiter calling on a non-Disputed lot (AwaitingDelivery) reverts WrongDeliveryState.
        _driveToAwaiting(address(0), ESCROW_E);

        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, ARB_PHOTO);

        assertEq(uint256(auction.getLot(LOT_ID).escrowAmount), ESCROW_E, "escrow untouched");
    }

    // resolveDispute is strictly lot-scoped: resolving LOT_ID leaves a second Disputed lot on the same
    // clone byte-for-byte untouched (no escrow, bond, or state change). Both lots are Disputed; only
    // LOT_ID is resolved.
    function test_ResolveDisputeCannotTouchAnotherLot() public {
        uint256 LOT_2 = 2;
        // both lots driven to Disputed on the same session (buyer opens each).
        _driveToDisputed(address(0), ESCROW_E, bidder1); // LOT_ID
        _driveSecondLotToDisputed(LOT_2, ESCROW_E, bidder1);

        // snapshot lot 2 before resolving lot 1.
        Lot memory lot2Before = auction.getLot(LOT_2);
        assertEq(uint8(lot2Before.deliveryState), uint8(DeliveryState.Disputed), "lot 2 precondition: Disputed");
        assertEq(uint256(lot2Before.escrowAmount), ESCROW_E, "lot 2 precondition: escrow == E");
        assertEq(uint256(lot2Before.disputeBond), uint256(DISPUTE_BOND_AMT), "lot 2 precondition: bond held");

        // resolve ONLY LOT_ID.
        vm.prank(arbiter);
        auction.resolveDispute(LOT_ID, Resolution.RefundToBuyer, ARB_PHOTO);

        // LOT_ID resolved; lot 2 is BYTE-FOR-BYTE unchanged (no cross-lot leakage).
        assertEq(uint8(auction.getLot(LOT_ID).phase), uint8(LotPhase.Refunded), "LOT_ID resolved to Refunded");

        Lot memory lot2After = auction.getLot(LOT_2);
        assertEq(uint8(lot2After.deliveryState), uint8(DeliveryState.Disputed), "lot 2 untouched: still Disputed");
        assertEq(uint8(lot2After.phase), uint8(LotPhase.Awaiting), "lot 2 untouched: still Awaiting");
        assertEq(uint256(lot2After.escrowAmount), ESCROW_E, "lot 2 untouched: escrow still E");
        assertEq(uint256(lot2After.disputeBond), uint256(DISPUTE_BOND_AMT), "lot 2 untouched: bond still held");
        assertEq(lot2After.disputeOpener, bidder1, "lot 2 untouched: opener preserved");
    }

    // No double-pay on the dispute path: after resolveDispute drives the lot to Released/Refunded,
    // deliveryState is no longer Disputed, so a second resolveDispute reverts WrongDeliveryState (the
    // state guard precedes the zero-escrow guard) and pays nothing more. The second call uses the
    // opposite resolution, the richest double-pay attempt.
    function test_RevertWhen_ResolveDisputeTwice() public {
        // direction 1: first ReleaseToSeller, then a second RefundToBuyer must revert + pay nothing.
        _resolveTwiceNoDoublePay(Resolution.ReleaseToSeller, Resolution.RefundToBuyer);
        // direction 2 (mirror): first RefundToBuyer, then a second ReleaseToSeller likewise.
        setUp();
        _resolveTwiceNoDoublePay(Resolution.RefundToBuyer, Resolution.ReleaseToSeller);
    }

    /// @dev Resolve a Disputed lot once with `first`, drain it fully, then attempt a SECOND resolve with
    ///      the opposite `second` resolution and assert it reverts WrongDeliveryState and moves zero wei.
    ///      The opener is the seller; the global drain (held == 0) holds regardless because the bond
    ///      winner is always paid in full on the first call. Native rail.
    function _resolveTwiceNoDoublePay(Resolution first, Resolution second) private {
        _driveToDisputed(address(0), ESCROW_E, seller); // seller opens the dispute

        // resolve once with `first`; the contract fully drains (escrow + bond both leave).
        vm.prank(arbiter);
        auction.resolveDispute(LOT_ID, first, ARB_PHOTO);

        Lot memory afterFirst = auction.getLot(LOT_ID);
        DeliveryState firstTerminal =
            first == Resolution.ReleaseToSeller ? DeliveryState.Released : DeliveryState.Refunded;
        LotPhase firstPhase = first == Resolution.ReleaseToSeller ? LotPhase.Settled : LotPhase.Refunded;
        assertEq(uint8(afterFirst.deliveryState), uint8(firstTerminal), "first resolve: terminal deliveryState");
        assertEq(uint8(afterFirst.phase), uint8(firstPhase), "first resolve: terminal phase");
        assertEq(uint256(afterFirst.escrowAmount), 0, "first resolve: escrow zeroed once");
        assertEq(uint256(afterFirst.disputeBond), 0, "first resolve: bond zeroed once");
        assertEq(address(auction).balance, 0, "first resolve: contract fully drained (escrow + bond)");

        // snapshot every payee before the must-fail second resolve: nothing can be paid again.
        uint256 sellerBefore = seller.balance;
        uint256 buyerBefore = bidder1.balance;
        uint256 feeRecipBefore = houseFeeRecipient.balance;
        uint256 contractBefore = address(auction).balance; // == 0 after the full drain

        // the opposite resolution is the richest double-pay attempt.
        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.resolveDispute(LOT_ID, second, ARB_PHOTO);

        // state is still the FIRST terminal (the second call flipped nothing) and NO second payout occurred.
        Lot memory afterSecond = auction.getLot(LOT_ID);
        assertEq(uint8(afterSecond.deliveryState), uint8(firstTerminal), "second resolve: deliveryState unchanged");
        assertEq(uint8(afterSecond.phase), uint8(firstPhase), "second resolve: phase unchanged");
        assertEq(uint256(afterSecond.escrowAmount), 0, "second resolve: escrow still zero");
        assertEq(uint256(afterSecond.disputeBond), 0, "second resolve: bond still zero");
        assertEq(seller.balance, sellerBefore, "second resolve: seller paid nothing more");
        assertEq(bidder1.balance, buyerBefore, "second resolve: buyer paid nothing more (never refunded)");
        assertEq(houseFeeRecipient.balance, feeRecipBefore, "second resolve: feeRecipient unchanged");
        assertEq(address(auction).balance, contractBefore, "second resolve: no second payout, contract still drained");
    }

    // Actor gates: markDelivered is seller-only, confirmReceipt/reclaimUndelivered are buyer-only; the
    // wrong actor reverts Unauthorized even with correct state and timing.
    function test_RevertWhen_D5WrongActor() public {
        // markDelivered by a non-seller (the buyer) in AwaitingDelivery -> Unauthorized.
        _driveToAwaiting(address(0), ESCROW_E);
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);

        // confirmReceipt by a non-buyer (the seller) in Delivered -> Unauthorized.
        setUp();
        _driveToDelivered(address(0), ESCROW_E);
        vm.prank(seller);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        // reclaimUndelivered by a non-buyer (the seller), timing satisfied -> Unauthorized.
        setUp();
        _driveToAwaiting(address(0), ESCROW_E);
        uint256 awaitingAt = uint256(auction.getLot(LOT_ID).awaitingAt);
        vm.warp(awaitingAt + SELLER_DELIVER_SEC);
        vm.prank(seller);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.reclaimUndelivered(LOT_ID);

        assertEq(uint256(auction.getLot(LOT_ID).escrowAmount), ESCROW_E, "escrow untouched");
    }

    // Release integrity gate: every seller-paying path re-checks that no bonded integrity dispute (Class
    // B) is open before releasing, because one can open after finalization. With one open, confirmReceipt
    // / releaseAfterWindow / resolveDispute(ReleaseToSeller) each revert BidIntegrityDisputeIsOpen; escrow
    // not zeroed, phase unchanged.
    function test_RevertWhen_ReleaseWithIntegrityDisputeOpen() public {
        _driveToDelivered(address(0), ESCROW_E);

        // a Class B challengeAttestation opens an integrity dispute on the winning seq after Delivered.
        _openClassBIntegrityDispute();

        // confirmReceipt (buyer) blocked.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.BidIntegrityDisputeIsOpen.selector);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        // releaseAfterWindow (keeper) blocked even past the window.
        uint256 deliveredAt = uint256(auction.getLot(LOT_ID).deliveredAt);
        vm.warp(deliveredAt + DISPUTE_WINDOW_SEC);
        vm.expectRevert(ISessionAuction.BidIntegrityDisputeIsOpen.selector);
        auction.releaseAfterWindow(LOT_ID);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), ESCROW_E, "escrow NOT zeroed");
        assertEq(uint8(lot.phase), uint8(LotPhase.Awaiting), "phase unchanged (not Settled)");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Delivered), "deliveryState stays Delivered");
    }

    function test_RevertWhen_ResolveReleaseWithIntegrityDisputeOpen() public {
        // resolveDispute(ReleaseToSeller) routes through _release and is equally gated.
        _driveToDisputed(address(0), ESCROW_E, seller);
        _openClassBIntegrityDispute();

        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.BidIntegrityDisputeIsOpen.selector);
        auction.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, ARB_PHOTO);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), ESCROW_E, "escrow NOT zeroed");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Disputed), "stays Disputed");
    }

    // The integrity gate is monotonic: clearing it re-enables release. After a Class B dispute opens on a
    // Delivered lot, clear the gate two ways (arbiter reject, then permissionless timeout); each time the
    // previously-blocked confirmReceipt settles (escrow zeroed, seller paid proceeds, fee routed, phase
    // Settled).
    function test_ReleaseSucceedsAfterIntegrityDisputeCleared() public {
        // (1) cleared by the arbiter REJECTING the Class B challenge (upheld == false, bond to seller).
        _releaseAfterIntegrityCleared(true /* clearByArbiterReject */);
        // (2) cleared by the permissionless TIMEOUT (silent challenge auto-resolved against the challenger).
        setUp();
        _releaseAfterIntegrityCleared(false /* clearByTimeout */);
    }

    function _releaseAfterIntegrityCleared(bool clearByArbiterReject) private {
        _driveToDelivered(address(0), ESCROW_E);
        uint64 seq = auction.getLot(LOT_ID).winnerSeq;
        _openClassBIntegrityDispute();

        // sanity: the gate is set (blocks release) before we clear it.
        assertTrue(auction.bidIntegrityDisputeOpen(LOT_ID), "integrity gate open before clear");

        if (clearByArbiterReject) {
            // arbiter rejects the Class B challenge (upheld == false): clears the gate, bond to seller.
            vm.prank(arbiter);
            auction.resolveBidIntegrityDispute(LOT_ID, seq, false, 0);
        } else {
            // permissionless timeout: auto-resolves the silent challenge, clearing the gate.
            vm.warp(block.timestamp + INTEGRITY_TIMEOUT_SEC + 1);
            auction.timeoutBidIntegrityDispute(LOT_ID, seq);
        }

        // the gate cleared: release is re-enabled.
        assertFalse(auction.bidIntegrityDisputeOpen(LOT_ID), "integrity gate cleared after resolve/timeout");

        uint256 fee = Math.mulDiv(ESCROW_E, FEE_BPS, 10_000);
        uint256 proceeds = ESCROW_E - fee;
        uint256 sellerBefore = seller.balance;
        uint256 feeRecipBefore = houseFeeRecipient.balance;

        // the previously-blocked seller-paying exit now settles cleanly.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);

        vm.prank(bidder1);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), 0, "post-clear: escrow zeroed");
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "post-clear: Settled");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Released), "post-clear: Released");
        assertEq(seller.balance - sellerBefore, proceeds, "post-clear: seller paid proceeds");
        assertEq(houseFeeRecipient.balance - feeRecipBefore, fee, "post-clear: feeRecipient paid fee");
    }

    // Integrity gate asymmetry: a Class B dispute gates only the seller-paying release, never the
    // buyer-paying refund. reclaimUndelivered and resolveDispute(RefundToBuyer) stay reachable while one
    // is open; a Class A challengeOverCeiling never gates release at all.
    function test_IntegrityGateDoesNotBlockRefund() public {
        // (1) AwaitingDelivery past sellerDeliverSec: reclaimUndelivered succeeds despite Class B open.
        _driveToAwaiting(address(0), ESCROW_E);
        _openClassBIntegrityDispute();
        uint256 awaitingAt = uint256(auction.getLot(LOT_ID).awaitingAt);
        vm.warp(awaitingAt + SELLER_DELIVER_SEC);

        uint256 buyerBefore = bidder1.balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Refunded(LOT_ID, bidder1, ESCROW_E);

        vm.prank(bidder1);
        auction.reclaimUndelivered(LOT_ID);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint8(lot.phase), uint8(LotPhase.Refunded), "refund reachable with Class B open");
        assertEq(uint256(lot.escrowAmount), 0, "escrow zeroed");
        assertEq(bidder1.balance - buyerBefore, ESCROW_E, "buyer refunded full escrow");

        // (2) Disputed: resolveDispute(RefundToBuyer) succeeds while a Class B dispute is open.
        setUp();
        _driveToDisputed(address(0), ESCROW_E, bidder1);
        _openClassBIntegrityDispute();

        uint256 buyer2Before = bidder1.balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Refunded(LOT_ID, bidder1, ESCROW_E);

        vm.prank(arbiter);
        auction.resolveDispute(LOT_ID, Resolution.RefundToBuyer, ARB_PHOTO);

        assertEq(uint8(auction.getLot(LOT_ID).phase), uint8(LotPhase.Refunded), "refund-resolution reachable");
        // buyer gets escrow + own bond back (opener wins on RefundToBuyer).
        assertEq(
            bidder1.balance - buyer2Before,
            uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT),
            "buyer refunded escrow + bond"
        );

        // (3) a Class A challengeOverCeiling does not freeze release: confirmReceipt still settles. A
        // valid Class A claim needs the winner over its committed ceiling (commit opens AND amount >
        // maxBid), so drive via _driveToDeliveredOverCeiling (commit binds E_OVER_MAXBID < ESCROW_E).
        // escrowAmount still snapshots the bid amount, so the fee/release math is unchanged; Class A
        // records harm but never sets the release gate.
        setUp();
        _driveToDeliveredOverCeiling(ESCROW_E);
        _openClassAOverCeiling();
        assertFalse(auction.bidIntegrityDisputeOpen(LOT_ID), "Class A never opens the _release gate");

        uint256 fee = Math.mulDiv(ESCROW_E, FEE_BPS, 10_000);
        uint256 proceeds = ESCROW_E - fee;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);

        vm.prank(bidder1);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        assertEq(uint8(auction.getLot(LOT_ID).phase), uint8(LotPhase.Settled), "Class A never freezes release");
    }

    // Fee math + dust to seller: fee == floor(amount*feeBps/10_000), proceeds == amount - fee,
    // proceeds + fee == amount exactly; the truncation remainder goes to the seller.
    function testFuzz_FeeMathDustToSeller(uint128 amount) public {
        // bound to a fundable escrow >= the lot reserve: a sub-reserve amount is not a reachable escrow
        // (placeBid reverts BidTooLow), and the dust/fee-floor property holds across the whole range.
        amount = uint128(bound(uint256(amount), RESERVE_PRICE, INITIAL_ETH / 2));

        _driveToDelivered(address(0), amount);

        uint256 fee = Math.mulDiv(amount, FEE_BPS, 10_000);
        uint256 proceeds = uint256(amount) - fee;
        assertEq(proceeds + fee, uint256(amount), "no wei created or lost (proceeds + fee == E)");
        // fee is the FLOOR: fee*10_000 never exceeds amount*FEE_BPS, and the truncation remainder
        // (the dust) is exactly what stays with the seller inside proceeds.
        assertLe(fee * 10_000, uint256(amount) * FEE_BPS, "fee floored (no over-charge)");
        uint256 dust = (uint256(amount) * FEE_BPS) % 10_000;
        assertEq(proceeds * 10_000, uint256(amount) * 10_000 - (uint256(amount) * FEE_BPS - dust), "dust to seller");

        uint256 sellerBefore = seller.balance;
        uint256 feeRecipBefore = houseFeeRecipient.balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);

        vm.prank(bidder1);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        // seller captures the truncation remainder (proceeds = amount - floor(fee)).
        assertEq(seller.balance - sellerBefore, proceeds, "seller gets proceeds incl dust");
        assertEq(houseFeeRecipient.balance - feeRecipBefore, fee, "feeRecipient gets floored fee");
        assertEq(uint256(auction.getLot(LOT_ID).escrowAmount), 0, "escrow zeroed");
    }

    // Zero-fee session: with feeBps == 0, release makes no fee transfer (the `if (fee != 0)` guard),
    // proceeds == amount, seller paid the full escrow, feeRecipient gets nothing, emits
    // Released(lotId, seller, escrow, 0).
    function test_ZeroFeeSession() public {
        InitConfig memory cfg = _defaultInitConfig(address(0));
        cfg.feeBps = 0;
        _initWithConfig(cfg);
        _driveToDeliveredPreInitialized(ESCROW_E);

        uint256 sellerBefore = seller.balance;
        uint256 feeRecipBefore = houseFeeRecipient.balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, ESCROW_E, 0);

        vm.prank(bidder1);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        assertEq(seller.balance - sellerBefore, uint256(ESCROW_E), "seller paid full E (no fee)");
        assertEq(houseFeeRecipient.balance - feeRecipBefore, 0, "feeRecipient gets nothing");
        assertEq(uint256(auction.getLot(LOT_ID).escrowAmount), 0, "escrow zeroed");
    }

    // Delivery entrypoints are not pausable: they execute while the contract is paused (none are
    // whenNotPaused), so a pause can never strand in-flight escrow.
    function test_D5NotPausable() public {
        _driveToDelivered(address(0), ESCROW_E);

        // pause the contract (pauser role). The release path must still complete.
        vm.prank(pauser);
        auction.pause();

        uint256 fee = Math.mulDiv(ESCROW_E, FEE_BPS, 10_000);
        uint256 proceeds = ESCROW_E - fee;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);

        // NOT EnforcedPause: confirmReceipt is not whenNotPaused, it settles while paused.
        vm.prank(bidder1);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "settled while paused");
        assertEq(uint256(lot.escrowAmount), 0, "escrow resolved while paused");
    }

    // Not pausable, exhaustively across all six delivery entrypoints. Each of markDelivered /
    // confirmReceipt / releaseAfterWindow / reclaimUndelivered / openDispute / resolveDispute is
    // exercised while paused and must complete its state flip + event (no EnforcedPause). Each segment
    // uses a fresh clone (setUp) and re-pauses; openDispute and resolveDispute (which move funds) get
    // full bond-pull / payout checks.
    function test_D5EntrypointsNotPausable() public {
        // (1) markDelivered (AwaitingDelivery -> Delivered) while paused.
        _driveToAwaiting(address(0), ESCROW_E);

        vm.prank(pauser);
        auction.pause();

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Delivered(LOT_ID, PROOF_HASH, DELIVERY_CID);

        vm.prank(seller);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID); // NOT EnforcedPause

        assertEq(uint8(auction.getLot(LOT_ID).deliveryState), uint8(DeliveryState.Delivered), "paused: markDelivered flips to Delivered");

        // (2) reclaimUndelivered (AwaitingDelivery -> Refunded, the buyer no-strand exit) while paused.
        setUp();
        _driveToAwaiting(address(0), ESCROW_E);
        uint256 awaitingAt = uint256(auction.getLot(LOT_ID).awaitingAt);
        vm.warp(awaitingAt + SELLER_DELIVER_SEC);

        vm.prank(pauser);
        auction.pause();

        uint256 buyerBeforeReclaim = bidder1.balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.ReclaimedUndelivered(LOT_ID, bidder1, ESCROW_E);

        vm.prank(bidder1);
        auction.reclaimUndelivered(LOT_ID); // NOT EnforcedPause

        assertEq(uint8(auction.getLot(LOT_ID).phase), uint8(LotPhase.Refunded), "paused: reclaimUndelivered refunds (no-strand exit)");
        assertEq(bidder1.balance - buyerBeforeReclaim, ESCROW_E, "paused: buyer refunded full escrow while paused");

        // (3) releaseAfterWindow (Delivered -> Settled) while paused.
        setUp();
        _driveToDelivered(address(0), ESCROW_E);
        uint256 deliveredAt = uint256(auction.getLot(LOT_ID).deliveredAt);
        vm.warp(deliveredAt + DISPUTE_WINDOW_SEC);

        vm.prank(pauser);
        auction.pause();

        uint256 fee = Math.mulDiv(ESCROW_E, FEE_BPS, 10_000);
        uint256 proceeds = ESCROW_E - fee;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.DeliveryAutoReleased(LOT_ID, seller);
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);

        vm.prank(bidder3); // permissionless keeper
        auction.releaseAfterWindow(LOT_ID); // NOT EnforcedPause

        assertEq(uint8(auction.getLot(LOT_ID).phase), uint8(LotPhase.Settled), "paused: releaseAfterWindow settles");

        // (4) openDispute (AwaitingDelivery -> Disputed) while paused: bond pulled.
        setUp();
        _driveToAwaiting(address(0), ESCROW_E);

        vm.prank(pauser);
        auction.pause();

        uint256 heldBeforeOpen = address(auction).balance;
        vm.deal(bidder1, bidder1.balance + uint256(DISPUTE_BOND_AMT));

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.DisputeOpened(LOT_ID, bidder1, DISPUTE_BOND_AMT, CLAIM_REF);

        vm.prank(bidder1);
        auction.openDispute{value: DISPUTE_BOND_AMT}(LOT_ID, CLAIM_REF); // NOT EnforcedPause

        Lot memory disputed = auction.getLot(LOT_ID);
        assertEq(uint8(disputed.deliveryState), uint8(DeliveryState.Disputed), "paused: openDispute freezes to Disputed");
        assertEq(uint256(disputed.disputeBond), uint256(DISPUTE_BOND_AMT), "paused: bond stored while paused");
        assertEq(address(auction).balance, heldBeforeOpen + uint256(DISPUTE_BOND_AMT), "paused: bond pulled in while paused");

        // (5) resolveDispute (Disputed -> Settled, arbiter path) while paused, full payout. Continue on
        // THIS already-Disputed lot (buyer opened above).
        uint256 sellerBeforeResolve = seller.balance;
        uint256 buyerBeforeResolve = bidder1.balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);
        // opener is the buyer; ReleaseToSeller means the opener loses, so the bond is forfeit to the
        // seller.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.DisputeResolved(LOT_ID, Resolution.ReleaseToSeller, seller);

        vm.prank(arbiter);
        auction.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, ARB_PHOTO); // NOT EnforcedPause

        Lot memory resolved = auction.getLot(LOT_ID);
        assertEq(uint8(resolved.phase), uint8(LotPhase.Settled), "paused: resolveDispute settles (arbiter path live)");
        assertEq(uint256(resolved.escrowAmount), 0, "paused: escrow released while paused");
        assertEq(uint256(resolved.disputeBond), 0, "paused: bond paid out while paused");
        // seller receives proceeds + bond, the losing opener (buyer) recovers nothing.
        assertEq(seller.balance - sellerBeforeResolve, proceeds + uint256(DISPUTE_BOND_AMT), "paused: seller paid proceeds + forfeited bond");
        assertEq(bidder1.balance, buyerBeforeResolve, "paused: losing opener (buyer) recovers nothing");

        // (6) confirmReceipt (Delivered -> Settled) while paused.
        setUp();
        _driveToDelivered(address(0), ESCROW_E);

        vm.prank(pauser);
        auction.pause();

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);

        vm.prank(bidder1);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID); // NOT EnforcedPause

        assertEq(uint8(auction.getLot(LOT_ID).phase), uint8(LotPhase.Settled), "paused: confirmReceipt settles");
    }

    // Delivery deadlines anchor on the frozen awaitingAt and deliveredAt, never on endsAt (which a
    // soft-close extension can slide forward).
    function test_D5AnchorsUseFrozenTimestamps() public {
        _driveToDelivered(address(0), ESCROW_E);

        Lot memory lot = auction.getLot(LOT_ID);
        uint256 awaitingAt = uint256(lot.awaitingAt);
        uint256 deliveredAt = uint256(lot.deliveredAt);
        uint256 endsAt = uint256(lot.endsAt);

        // the delivery anchors are distinct from the (soft-close-slidable) endsAt.
        assertTrue(awaitingAt != 0, "awaitingAt set at finalizeWinner");
        assertTrue(deliveredAt != 0, "deliveredAt set at markDelivered");

        // releaseAfterWindow keys on deliveredAt + disputeWindowSec, independent of endsAt: one second
        // before the deliveredAt-anchored boundary it still reverts NotElapsed, even though that instant
        // is well past endsAt.
        vm.warp(deliveredAt + DISPUTE_WINDOW_SEC - 1);
        assertGt(block.timestamp, endsAt, "past endsAt yet the window is not elapsed");
        vm.expectRevert(ISessionAuction.DisputeWindowNotElapsed.selector);
        auction.releaseAfterWindow(LOT_ID);

        // exactly at the deliveredAt-anchored boundary it releases.
        vm.warp(deliveredAt + DISPUTE_WINDOW_SEC);
        vm.prank(bidder3);
        auction.releaseAfterWindow(LOT_ID);
        assertEq(uint8(auction.getLot(LOT_ID).phase), uint8(LotPhase.Settled), "auto-release anchored on deliveredAt");
    }

    // Terminal exhaustiveness + idempotency: from a Settled/Refunded terminal every delivery call
    // reverts; a second markDelivered reverts WrongDeliveryState; confirmReceipt from AwaitingDelivery
    // reverts WrongDeliveryState.
    function test_D5TerminalExhaustiveness() public {
        // drive to a Settled terminal via confirmReceipt, then assert every re-entry reverts.
        _driveToDelivered(address(0), ESCROW_E);
        vm.prank(bidder1);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);
        assertEq(uint8(auction.getLot(LOT_ID).phase), uint8(LotPhase.Settled), "Settled terminal");

        // markDelivered from a terminal -> WrongDeliveryState.
        vm.prank(seller);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);

        // confirmReceipt again -> WrongDeliveryState (no longer Delivered).
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        // reclaimUndelivered from a terminal -> WrongDeliveryState.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.reclaimUndelivered(LOT_ID);

        // releaseAfterWindow from a terminal -> WrongDeliveryState.
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.releaseAfterWindow(LOT_ID);
    }

    function test_RevertWhen_MarkDeliveredTwice() public {
        // first markDelivered moves to Delivered; a second reverts WrongDeliveryState (one-shot).
        _driveToAwaiting(address(0), ESCROW_E);

        vm.prank(seller);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);
        assertEq(uint8(auction.getLot(LOT_ID).deliveryState), uint8(DeliveryState.Delivered), "Delivered");

        vm.prank(seller);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);
    }

    function test_RevertWhen_ConfirmFromAwaitingDelivery() public {
        // confirmReceipt is legal ONLY from Delivered; from AwaitingDelivery it reverts WrongDeliveryState.
        _driveToAwaiting(address(0), ESCROW_E);

        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        assertEq(uint256(auction.getLot(LOT_ID).escrowAmount), ESCROW_E, "escrow untouched");
    }

    // Griefing-bond economics: a bad-faith opener forfeits the bond to the honest counterparty across
    // all four opener x resolution combos; the loser never recovers it; bondRecipient in
    // DisputeResolved matches the honest party; the bond never touches escrowAmount.
    function test_GriefingBondToHonestParty() public {
        // (buyer, RefundToBuyer) -> buyer wins, gets bond back.
        _griefCase(bidder1, Resolution.RefundToBuyer, bidder1);
        // (buyer, ReleaseToSeller) -> buyer loses, bond forfeit to seller.
        setUp();
        _griefCase(bidder1, Resolution.ReleaseToSeller, seller);
        // (seller, ReleaseToSeller) -> seller wins, gets bond back.
        setUp();
        _griefCase(seller, Resolution.ReleaseToSeller, seller);
        // (seller, RefundToBuyer) -> seller loses, bond forfeit to buyer.
        setUp();
        _griefCase(seller, Resolution.RefundToBuyer, bidder1);
    }

    function _griefCase(address opener, Resolution res, address bondRecipient) private {
        _driveToDisputed(address(0), ESCROW_E, opener);

        // the loser is whichever party is NOT the bondRecipient; snapshot to prove no recovery.
        address loser = bondRecipient == seller ? bidder1 : seller;
        uint256 loserBefore = loser.balance;
        uint256 recipBefore = bondRecipient.balance;
        uint256 escrowHeldBefore = address(auction).balance; // escrow E + bond, both native here

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.DisputeResolved(LOT_ID, res, bondRecipient);

        vm.prank(arbiter);
        auction.resolveDispute(LOT_ID, res, ARB_PHOTO);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.disputeBond), 0, "bond zeroed (separate pool, never escrowAmount)");
        assertEq(uint256(lot.escrowAmount), 0, "escrow zeroed exactly once");

        // the bond went to the honest/winning party. The loser may also be the escrow payee, so the bond
        // is shown not to flow to them only when the loser is not the escrow payee.
        assertGe(bondRecipient.balance - recipBefore, uint256(DISPUTE_BOND_AMT), "bond to honest party");

        if (loser != _escrowPayee(res)) {
            assertEq(loser.balance - loserBefore, 0, "loser recovers nothing");
        }

        // every wei held (escrow + bond) left the contract; nothing stranded.
        assertEq(
            escrowHeldBefore, address(auction).balance + uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT), "no strand"
        );
    }

    function _escrowPayee(Resolution res) private view returns (address) {
        return res == Resolution.ReleaseToSeller ? seller : bidder1;
    }

    // Delivery entry state: finalizeWinner sets awaitingAt, flips deliveryState to AwaitingDelivery,
    // carries escrowAmount unchanged, and emits WinnerFinalized.
    function test_D5EntryStateAfterFinalize() public {
        // drive to Hammered + revealed + AC window closed, then finalize with the entry assertion.
        _driveToHammeredRevealed(address(0), ESCROW_E);

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.WinnerFinalized(LOT_ID, bidder1, ESCROW_E);

        auction.finalizeWinner(LOT_ID);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.AwaitingDelivery), "entry: AwaitingDelivery");
        assertEq(uint8(lot.phase), uint8(LotPhase.Awaiting), "entry: phase Awaiting");
        assertEq(uint256(lot.awaitingAt), block.timestamp, "entry: awaitingAt == now (frozen anchor)");
        assertEq(uint256(lot.escrowAmount), ESCROW_E, "entry: escrowAmount == E (no re-lock)");
        assertEq(lot.highBidder, bidder1, "entry: buyer == promoted/finalized winner");
    }

    // A voided-and-promoted winner enters the identical AwaitingDelivery node with no special-casing.
    // Drive Hammered -> Voided (voidAndAward) -> Awaiting (finalizeWinner) with bidder1 as the promoted
    // winner, then run the full markDelivered -> confirmReceipt release and assert the same escrow + fee
    // routing as a clean winner.
    function test_PromotedWinnerD5SettlesIdentically() public {
        _driveToAwaitingViaVoid(ESCROW_E); // Voided -> Awaiting, promoted winner == bidder1

        // entry is identical to a clean winner: AwaitingDelivery, escrow carried, awaitingAt set.
        Lot memory entry = auction.getLot(LOT_ID);
        assertEq(uint8(entry.deliveryState), uint8(DeliveryState.AwaitingDelivery), "promoted: AwaitingDelivery");
        assertEq(uint256(entry.escrowAmount), ESCROW_E, "promoted: escrow == E carried into delivery");
        assertEq(entry.highBidder, bidder1, "promoted winner is the buyer");

        // full delivery settlement on the promoted winner: markDelivered then confirmReceipt -> Released.
        vm.prank(seller);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);

        uint256 fee = Math.mulDiv(ESCROW_E, FEE_BPS, 10_000);
        uint256 proceeds = ESCROW_E - fee;
        uint256 sellerBefore = seller.balance;
        uint256 feeRecipBefore = houseFeeRecipient.balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);

        vm.prank(bidder1);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), 0, "promoted: escrow zeroed identically");
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "promoted: Settled identically");
        assertEq(seller.balance - sellerBefore, proceeds, "promoted: seller paid proceeds identically");
        assertEq(houseFeeRecipient.balance - feeRecipBefore, fee, "promoted: fee routed identically");
    }

    // openDispute on a Delivered lot must succeed at the last legal instant, deliveredAt +
    // disputeWindowSec - 1 (the guard is a strict `<`). Pairs with test_RevertWhen_DisputeAfterWindow,
    // which warps to the exact boundary and asserts DisputeWindowElapsed, to pin `<` vs `<=`.
    function test_OpenDisputeAtLastLegalSecond() public {
        _driveToDelivered(address(0), ESCROW_E);
        uint256 deliveredAt = uint256(auction.getLot(LOT_ID).deliveredAt);

        vm.warp(deliveredAt + DISPUTE_WINDOW_SEC - 1); // one second before the window lapses

        uint256 heldBefore = address(auction).balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.DisputeOpened(LOT_ID, bidder1, DISPUTE_BOND_AMT, CLAIM_REF);

        vm.deal(bidder1, bidder1.balance + uint256(DISPUTE_BOND_AMT));
        vm.prank(bidder1);
        auction.openDispute{value: DISPUTE_BOND_AMT}(LOT_ID, CLAIM_REF);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Disputed), "last-legal-second: Disputed");
        assertEq(lot.disputeOpener, bidder1, "last-legal-second: opener stored");
        assertEq(uint256(lot.disputeBond), uint256(DISPUTE_BOND_AMT), "last-legal-second: bond stored");
        assertEq(uint256(lot.escrowAmount), ESCROW_E, "last-legal-second: escrow frozen, untouched");
        assertEq(
            address(auction).balance, heldBefore + uint256(DISPUTE_BOND_AMT), "last-legal-second: only bond pulled"
        );
    }

    // resolveDispute routes escrow + bond identically from a Delivered-origin dispute (seller already
    // marked delivered) for both resolutions. The {AwaitingDelivery, Delivered} -> Disputed transition
    // has two entries; this exercises the Delivered one.
    function test_ResolveDisputeFromDeliveredOrigin() public {
        // ReleaseToSeller from a Delivered-origin dispute opened by the seller (opener wins, bond back).
        _resolveFromDeliveredOrigin(seller, Resolution.ReleaseToSeller);
        // RefundToBuyer from a Delivered-origin dispute opened by the buyer (opener wins, bond back).
        setUp();
        _resolveFromDeliveredOrigin(bidder1, Resolution.RefundToBuyer);
    }

    function _resolveFromDeliveredOrigin(address opener, Resolution res) private {
        _driveToDisputedFrom(
            address(0),
            ESCROW_E,
            opener,
            true /* viaDelivered */
        );

        // Delivered-origin precondition: the dispute carries a nonzero deliveredAt anchor.
        assertTrue(uint256(auction.getLot(LOT_ID).deliveredAt) != 0, "delivered-origin: deliveredAt set");

        uint256 fee = Math.mulDiv(ESCROW_E, FEE_BPS, 10_000);
        uint256 proceeds = ESCROW_E - fee;

        if (res == Resolution.ReleaseToSeller) {
            uint256 sellerBefore = seller.balance; // opener == seller here, so seller gets proceeds + bond
            vm.expectEmit(true, true, true, true, address(auction));
            emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);
            vm.expectEmit(true, true, true, true, address(auction));
            emit ISessionAuction.DisputeResolved(LOT_ID, Resolution.ReleaseToSeller, seller);

            vm.prank(arbiter);
            auction.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, ARB_PHOTO);

            Lot memory lot = auction.getLot(LOT_ID);
            assertEq(uint256(lot.escrowAmount), 0, "delivered-origin release: escrow zeroed");
            assertEq(uint256(lot.disputeBond), 0, "delivered-origin release: bond zeroed");
            assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "delivered-origin release: Settled");
            assertEq(
                seller.balance - sellerBefore,
                proceeds + uint256(DISPUTE_BOND_AMT),
                "delivered-origin: seller proceeds + bond"
            );
        } else {
            uint256 buyerBefore = bidder1.balance; // opener == buyer here, so buyer gets escrow + bond
            vm.expectEmit(true, true, true, true, address(auction));
            emit ISessionAuction.Refunded(LOT_ID, bidder1, ESCROW_E);
            vm.expectEmit(true, true, true, true, address(auction));
            emit ISessionAuction.DisputeResolved(LOT_ID, Resolution.RefundToBuyer, bidder1);

            vm.prank(arbiter);
            auction.resolveDispute(LOT_ID, Resolution.RefundToBuyer, ARB_PHOTO);

            Lot memory lot = auction.getLot(LOT_ID);
            assertEq(uint256(lot.escrowAmount), 0, "delivered-origin refund: escrow zeroed");
            assertEq(uint256(lot.disputeBond), 0, "delivered-origin refund: bond zeroed");
            assertEq(uint8(lot.phase), uint8(LotPhase.Refunded), "delivered-origin refund: Refunded");
            assertEq(
                bidder1.balance - buyerBefore,
                uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT),
                "delivered-origin: buyer escrow + bond"
            );
        }
    }

    // openDispute from a terminal phase reverts WrongDeliveryState and pulls no bond. Covers Settled
    // (post-confirm) and Refunded (post-reclaim), each by a real party (so the revert is the state guard,
    // not Unauthorized).
    function test_RevertWhen_OpenDisputeFromTerminalPhase() public {
        // (1) Settled terminal: confirmReceipt has released the escrow.
        _driveToDelivered(address(0), ESCROW_E);
        vm.prank(bidder1);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);
        assertEq(uint8(auction.getLot(LOT_ID).phase), uint8(LotPhase.Settled), "Settled terminal reached");

        uint256 heldBeforeSettled = address(auction).balance;

        vm.deal(seller, seller.balance + uint256(DISPUTE_BOND_AMT));
        vm.prank(seller); // a real party (seller), so the revert is the state guard, not Unauthorized
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.openDispute{value: DISPUTE_BOND_AMT}(LOT_ID, CLAIM_REF);
        assertEq(address(auction).balance, heldBeforeSettled, "Settled: no bond pulled in");

        // (2) Refunded terminal: reclaimUndelivered has refunded the buyer.
        setUp();
        _driveToAwaiting(address(0), ESCROW_E);
        uint256 awaitingAt = uint256(auction.getLot(LOT_ID).awaitingAt);
        vm.warp(awaitingAt + SELLER_DELIVER_SEC);
        vm.prank(bidder1);
        auction.reclaimUndelivered(LOT_ID);
        assertEq(uint8(auction.getLot(LOT_ID).phase), uint8(LotPhase.Refunded), "Refunded terminal reached");

        uint256 heldBeforeRefunded = address(auction).balance;

        vm.deal(bidder1, bidder1.balance + uint256(DISPUTE_BOND_AMT));
        vm.prank(bidder1); // a real party (buyer)
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.openDispute{value: DISPUTE_BOND_AMT}(LOT_ID, CLAIM_REF);
        assertEq(address(auction).balance, heldBeforeRefunded, "Refunded: no bond pulled in");
    }

    // resolveDispute photoHash is event-only and gates nothing: resolving with photoHash == bytes32(0)
    // yields the identical resolution + payout (a nonzero photoHash is never required).
    function test_ResolveDisputeZeroPhotoHashGatesNothing() public {
        _driveToDisputed(address(0), ESCROW_E, bidder1); // buyer opens, then wins RefundToBuyer

        uint256 buyerBefore = bidder1.balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Refunded(LOT_ID, bidder1, ESCROW_E);
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.DisputeResolved(LOT_ID, Resolution.RefundToBuyer, bidder1);

        vm.prank(arbiter);
        auction.resolveDispute(LOT_ID, Resolution.RefundToBuyer, bytes32(0)); // photoHash == 0

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), 0, "zero-photo: escrow zeroed");
        assertEq(uint256(lot.disputeBond), 0, "zero-photo: bond zeroed");
        assertEq(uint8(lot.phase), uint8(LotPhase.Refunded), "zero-photo: Refunded");
        assertEq(
            bidder1.balance - buyerBefore, uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT), "zero-photo: identical payout"
        );
    }

    // Deterministic fee-floor math at two fixed example amounts (FEE_BPS == 250).
    //   amount = 10_001 (non-divisible): fee == floor(10_001*250/10_000) == 250, proceeds == 9_751,
    //     proceeds + fee == 10_001 (dust to seller).
    //   amount = 39: fee floors to 0, proceeds == 39, no fee transfer.
    //   Both run on a reserve-1 lot so the sub-reserve amounts can clear hammer.
    function test_FeeMathNamedWitnessNonDivisible() public {
        uint128 amount = 10_001;
        _driveToDeliveredWithReserve(address(0), amount, 1);

        uint256 fee = Math.mulDiv(amount, FEE_BPS, 10_000);
        uint256 proceeds = uint256(amount) - fee;
        assertEq(fee, 250, "witness: fee == floor(10_001*250/10_000) == 250");
        assertEq(proceeds, 9_751, "witness: proceeds == 9_751");
        assertEq(proceeds + fee, uint256(amount), "witness: proceeds + fee == 10_001");

        uint256 sellerBefore = seller.balance;
        uint256 feeRecipBefore = houseFeeRecipient.balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);

        vm.prank(bidder1);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        assertEq(seller.balance - sellerBefore, proceeds, "witness: seller gets 9_751 (incl dust)");
        assertEq(houseFeeRecipient.balance - feeRecipBefore, fee, "witness: feeRecipient gets 250");
        assertEq(uint256(auction.getLot(LOT_ID).escrowAmount), 0, "witness: escrow zeroed");
    }

    function test_FeeMathFloorsToZeroNoFeeTransfer() public {
        uint128 amount = 39; // 39 * 250 / 10_000 == floor(0.975) == 0
        _driveToDeliveredWithReserve(address(0), amount, 1);

        uint256 fee = Math.mulDiv(amount, FEE_BPS, 10_000);
        assertEq(fee, 0, "floor: sub-dust amount floors fee to 0");

        uint256 sellerBefore = seller.balance;
        uint256 feeRecipBefore = houseFeeRecipient.balance;

        // fee == 0 -> the `if (fee != 0)` guard skips the fee transfer; Released carries fee == 0.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, seller, uint256(amount), 0);

        vm.prank(bidder1);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        assertEq(seller.balance - sellerBefore, uint256(amount), "floor: seller gets the FULL amount (no fee)");
        assertEq(houseFeeRecipient.balance - feeRecipBefore, 0, "floor: NO fee transfer");
        assertEq(uint256(auction.getLot(LOT_ID).escrowAmount), 0, "floor: escrow zeroed");
    }

    // No double-pay on confirmReceipt: it is nonReentrant and _release follows checks-effects-
    // interactions (escrow zeroed + state flipped before the payouts). A reentrant seller (re-entering
    // from receive() during the proceeds push) has its nested call rejected by the guard, while the outer
    // terminal completes exactly once (escrow zeroed, Settled, Released, seller paid once).
    function test_ReentrantConfirmReceiptCannotDoublePay() public {
        // owner_ is unused here (the EOA bidder1 places the bid; the contract is only the seller).
        E_ReentrantParty attackerSeller = new E_ReentrantParty(bidder1);
        // a Delivered lot whose seller is the reentrant contract (buyer is the usual bidder1).
        _driveToDeliveredWith(ESCROW_E, bidder1, address(attackerSeller));

        // arm the seller to re-enter releaseAfterWindow when it receives the proceeds; the contract-global
        // transient guard makes the nested ReentrancyGuardReentrantCall hold regardless of modifier order,
        // proving confirmReceipt holds the guard.
        attackerSeller.arm(auction, LOT_ID);

        uint256 fee = Math.mulDiv(ESCROW_E, FEE_BPS, 10_000);
        uint256 proceeds = ESCROW_E - fee;
        uint256 sellerBefore = address(attackerSeller).balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, address(attackerSeller), proceeds, fee);

        vm.prank(bidder1);
        auction.confirmReceipt(LOT_ID, PHOTO_HASH, PHOTO_CID);

        // the nested re-entrant confirmReceipt was rejected by the reentrancy guard.
        assertEq(
            attackerSeller.reentrySelector(),
            ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector,
            "nested call must hit ReentrancyGuardReentrantCall"
        );

        // the OUTER terminal completed exactly once: escrow zeroed, Settled, seller paid a single time.
        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), 0, "no-double-pay: escrow zeroed exactly once");
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "no-double-pay: Settled");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Released), "no-double-pay: Released");
        assertEq(
            address(attackerSeller).balance - sellerBefore, proceeds, "no-double-pay: seller paid proceeds exactly once"
        );
    }

    // No double-pay on resolveDispute, the richest checks-effects-interactions terminal: it is
    // nonReentrant and sequences bond-zero + _release (escrow-zero + state flip) before any external
    // push. A reentrant seller is rejected by the guard, while the outer resolution completes once
    // (escrow + bond zeroed, Settled, seller paid proceeds + bond once). opener == seller plus
    // ReleaseToSeller means the seller wins and receives both.
    function test_ReentrantResolveDisputeCannotDoublePay() public {
        // owner_ is unused here (the EOA bidder1 places the bid; the contract is only the seller).
        E_ReentrantParty attackerSeller = new E_ReentrantParty(bidder1);
        // a Disputed lot whose seller (and dispute opener) is the reentrant contract; buyer == bidder1.
        _driveToDisputedWithSeller(ESCROW_E, address(attackerSeller));

        // arm the seller to re-enter releaseAfterWindow on the proceeds push; the contract-global guard
        // makes the nested ReentrancyGuardReentrantCall hold under any modifier order, proving
        // resolveDispute holds it.
        attackerSeller.arm(auction, LOT_ID);

        uint256 fee = Math.mulDiv(ESCROW_E, FEE_BPS, 10_000);
        uint256 proceeds = ESCROW_E - fee;
        uint256 sellerBefore = address(attackerSeller).balance;

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Released(LOT_ID, address(attackerSeller), proceeds, fee);
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.DisputeResolved(LOT_ID, Resolution.ReleaseToSeller, address(attackerSeller));

        vm.prank(arbiter);
        auction.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, ARB_PHOTO);

        // the nested re-entrant call was rejected by the reentrancy guard.
        assertEq(
            attackerSeller.reentrySelector(),
            ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector,
            "nested resolve must hit ReentrancyGuardReentrantCall"
        );

        // OUTER resolution completed once: escrow + bond zeroed, Settled, seller paid proceeds + bond once.
        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), 0, "no-double-pay: escrow zeroed once");
        assertEq(uint256(lot.disputeBond), 0, "no-double-pay: bond zeroed once (CEI)");
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "no-double-pay: Settled");
        assertEq(
            address(attackerSeller).balance - sellerBefore,
            proceeds + uint256(DISPUTE_BOND_AMT),
            "no-double-pay: seller paid proceeds + bond exactly once"
        );
    }

    // No double-pay on the buyer-side refund terminal: the buyer-side counterpart of
    // test_ReentrantConfirmReceiptCannotDoublePay. reclaimUndelivered is nonReentrant and its only
    // external push is _refund(highBidder). The buyer is the reentrant contract: it re-enters
    // releaseAfterWindow from receive() during the escrow push; the guard trips the nested call, while
    // the outer reclaim completes exactly once (escrow zeroed, Refunded, buyer paid ESCROW_E once,
    // contract drained).
    function test_ReentrantReclaimUndeliveredCannotDoublePay() public {
        // owner_ == bidder1: this contract is the recorded bid principal, and the ceiling envelope is
        // signed with bidder1Key, so its ERC-1271 isValidSignature recovers the bid signature to bidder1.
        E_ReentrantParty attackerBuyer = new E_ReentrantParty(bidder1);
        // an AwaitingDelivery lot whose buyer is the reentrant contract (seller is the usual EOA).
        _driveToAwaitingWith(ESCROW_E, address(attackerBuyer), seller);

        // arm the buyer to re-enter releaseAfterWindow on the refund push; the contract-global guard makes
        // the nested ReentrancyGuardReentrantCall hold under any modifier order, proving reclaimUndelivered
        // holds it.
        attackerBuyer.arm(auction, LOT_ID);

        // warp to the exact reclaim boundary (awaitingAt + sellerDeliverSec): the buyer's no-strand exit.
        uint256 awaitingAt = uint256(auction.getLot(LOT_ID).awaitingAt);
        vm.warp(awaitingAt + SELLER_DELIVER_SEC);

        uint256 buyerBefore = address(attackerBuyer).balance;
        uint256 heldBefore = address(auction).balance; // exactly the escrow (no bond in this state)
        assertEq(heldBefore, uint256(ESCROW_E), "pre-reclaim: contract holds exactly the escrow");

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.ReclaimedUndelivered(LOT_ID, address(attackerBuyer), ESCROW_E);
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Refunded(LOT_ID, address(attackerBuyer), ESCROW_E);

        vm.prank(address(attackerBuyer));
        auction.reclaimUndelivered(LOT_ID);

        // the nested re-entrant releaseAfterWindow was rejected by the reentrancy guard.
        assertEq(
            attackerBuyer.reentrySelector(),
            ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector,
            "nested reclaim re-entry must hit ReentrancyGuardReentrantCall"
        );

        // the OUTER terminal completed exactly once: escrow zeroed, Refunded, buyer refunded ESCROW_E once.
        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), 0, "no-double-pay: escrow zeroed exactly once");
        assertEq(uint8(lot.phase), uint8(LotPhase.Refunded), "no-double-pay: Refunded");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Refunded), "no-double-pay: deliveryState Refunded");
        assertEq(
            address(attackerBuyer).balance - buyerBefore, uint256(ESCROW_E), "no-double-pay: buyer refunded ESCROW_E exactly once"
        );
        // the FULL escrow (and nothing else) left the contract: no double-refund, no strand.
        assertEq(address(auction).balance, 0, "no-double-pay: contract fully drained (escrow only)");
        assertEq(heldBefore - address(auction).balance, uint256(ESCROW_E), "no-double-pay: held dropped by exactly the escrow");
    }

    // No double-pay on resolveDispute(RefundToBuyer): the RefundToBuyer counterpart of
    // test_ReentrantResolveDisputeCannotDoublePay, the other refund terminal that pushes the full escrow
    // to a contract buyer. The buyer is both the reentrant contract and the dispute opener, so the opener
    // wins on RefundToBuyer and receives escrow + bond. It re-enters releaseAfterWindow from receive() on
    // the escrow push (and again on the bond push); the guard trips the nested call, while the outer
    // resolution completes once (escrow + bond zeroed, Refunded, buyer paid escrow + bond once, contract
    // drained).
    function test_ReentrantResolveRefundToBuyerCannotDoublePay() public {
        // owner_ == bidder1: this contract is the recorded bid principal, and the ceiling envelope is
        // signed with bidder1Key, so its ERC-1271 isValidSignature recovers the bid signature to bidder1.
        E_ReentrantParty attackerBuyer = new E_ReentrantParty(bidder1);
        // a Disputed lot whose buyer (and dispute opener) is the reentrant contract; seller == the EOA.
        _driveToDisputedWithBuyer(ESCROW_E, address(attackerBuyer));

        // arm the buyer to re-enter releaseAfterWindow on the refund/bond pushes; the contract-global
        // guard makes the nested ReentrancyGuardReentrantCall hold under any modifier order, proving
        // resolveDispute holds it.
        attackerBuyer.arm(auction, LOT_ID);

        uint256 buyerBefore = address(attackerBuyer).balance;
        uint256 heldBefore = address(auction).balance; // escrow + bond, both native
        assertEq(heldBefore, uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT), "pre-resolve: held == escrow + bond");

        // opener == buyer and resolution == RefundToBuyer => the opener WINS: bond returns to the buyer,
        // so bondRecipient == the buyer (the reentrant contract); buyer receives escrow + bond.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.Refunded(LOT_ID, address(attackerBuyer), ESCROW_E);
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.DisputeResolved(LOT_ID, Resolution.RefundToBuyer, address(attackerBuyer));

        vm.prank(arbiter);
        auction.resolveDispute(LOT_ID, Resolution.RefundToBuyer, ARB_PHOTO);

        // the nested re-entrant releaseAfterWindow was rejected by the reentrancy guard.
        assertEq(
            attackerBuyer.reentrySelector(),
            ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector,
            "nested refund-resolve re-entry must hit ReentrancyGuardReentrantCall"
        );

        // OUTER resolution completed once: escrow + bond zeroed, Refunded, buyer paid escrow + bond once.
        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.escrowAmount), 0, "no-double-pay: escrow zeroed once");
        assertEq(uint256(lot.disputeBond), 0, "no-double-pay: bond zeroed once (CEI)");
        assertEq(uint8(lot.phase), uint8(LotPhase.Refunded), "no-double-pay: Refunded");
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.Refunded), "no-double-pay: deliveryState Refunded");
        assertEq(
            address(attackerBuyer).balance - buyerBefore,
            uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT),
            "no-double-pay: buyer paid escrow + bond exactly once"
        );
        // every wei held (escrow + bond) left the contract exactly once: no double-refund, no strand.
        assertEq(address(auction).balance, 0, "no-double-pay: contract fully drained (escrow + bond)");
        assertEq(
            heldBefore - address(auction).balance,
            uint256(ESCROW_E) + uint256(DISPUTE_BOND_AMT),
            "no-double-pay: held dropped by exactly escrow + bond"
        );
    }

    // openDispute is nonReentrant: its bond pull uses the bubbling SafeERC20.safeTransferFrom, so a
    // hostile payment token whose transferFrom re-enters a nonReentrant delivery function makes the
    // nested ReentrancyGuardReentrantCall propagate and revert the outer openDispute. No dispute is
    // opened and no escrow moves.
    function test_RevertWhen_OpenDisputeReentered() public {
        E_ReentrantPullERC20 evilToken = new E_ReentrantPullERC20();
        // Awaiting lot on the reentrant-token rail; buyer == bidder1 is the dispute opener.
        SessionAuction a = _awaitingOnToken(evilToken, ESCROW_E, bidder1);

        // fund + approve the bond, then arm the token to re-enter during the bond pull.
        evilToken.mint(bidder1, uint256(DISPUTE_BOND_AMT));
        vm.prank(bidder1);
        evilToken.approve(address(a), DISPUTE_BOND_AMT);
        // re-enter releaseAfterWindow during the bond pull; the nested ReentrancyGuardReentrantCall
        // bubbles through safeTransferFrom and reverts the outer openDispute.
        evilToken.arm(a, abi.encodeWithSelector(ISessionAuction.releaseAfterWindow.selector, LOT_ID));

        uint256 heldBefore = evilToken.balanceOf(address(a));

        vm.prank(bidder1);
        vm.expectRevert(ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector);
        a.openDispute(LOT_ID, CLAIM_REF);

        // the whole tx reverted: no dispute opened, no bond pulled, escrow untouched.
        Lot memory lot = a.getLot(LOT_ID);
        assertEq(uint8(lot.deliveryState), uint8(DeliveryState.AwaitingDelivery), "reentered open: no transition");
        assertEq(uint256(lot.disputeBond), 0, "reentered open: no bond stored");
        assertEq(uint256(lot.escrowAmount), ESCROW_E, "reentered open: escrow untouched");
        assertEq(evilToken.balanceOf(address(a)), heldBefore, "reentered open: no bond pulled in");
    }

    // A hostile bond winner cannot strand the resolution: the bond payout has its own checks-effects-
    // interactions, so a winner that cannot accept the push is credited to pendingWithdrawals and the
    // resolution still completes. The bond winner is also the escrow payee, so the parked amount is the
    // escrow payout + bond; WithdrawalCredited(winner, bond) is asserted by its distinct amount. Run
    // native (hostile contract winner) and ERC-20 (false-return token), then recover via claimPending.
    function test_HostileBondWinnerCreditedNoStrand() public {
        _hostileBondWinnerNative();
        _hostileBondWinnerToken();
    }

    /// @dev Native rail: the WINNER (seller, opener, ReleaseToSeller) is a contract that rejects pushes.
    ///      Both the proceeds and the bond push fail and park to the seller; the fee still pays the
    ///      feeRecipient; resolveDispute completes. The EOA buyer (bidder1) places the bid.
    function _hostileBondWinnerNative() private {
        E_RejectingReceiver hostileSeller = new E_RejectingReceiver();
        _driveToDisputedWithSeller(ESCROW_E, address(hostileSeller)); // seller opens; seller will WIN release

        uint256 fee = Math.mulDiv(ESCROW_E, FEE_BPS, 10_000);
        uint256 proceeds = ESCROW_E - fee;
        uint256 parked = proceeds + uint256(DISPUTE_BOND_AMT); // proceeds + bond both to the seller
        uint256 feeRecipBefore = houseFeeRecipient.balance;

        // assert the bond credit by its amount (== bond) so it matches the bond leg, not the proceeds
        // leg; resolveDispute must not revert.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.WithdrawalCredited(address(hostileSeller), uint256(DISPUTE_BOND_AMT));

        vm.prank(arbiter);
        auction.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, ARB_PHOTO);

        Lot memory lot = auction.getLot(LOT_ID);
        assertEq(uint256(lot.disputeBond), 0, "native hostile-bond: bond zeroed");
        assertEq(uint256(lot.escrowAmount), 0, "native hostile-bond: escrow zeroed");
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "native hostile-bond: resolution completed (Settled)");
        assertEq(
            auction.pendingWithdrawal(address(hostileSeller)),
            parked,
            "native hostile-bond: proceeds + bond parked, no strand"
        );
        // the healthy feeRecipient is still paid normally (the hostile winner cannot strand the fee).
        assertEq(houseFeeRecipient.balance - feeRecipBefore, fee, "native hostile-bond: feeRecipient still paid");

        // recoverable: toggle the receiver to accept, claimPending pulls the full parked amount.
        hostileSeller.setReject(false);
        uint256 balBefore = address(hostileSeller).balance;
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.WithdrawalClaimed(address(hostileSeller), parked);
        vm.prank(address(hostileSeller));
        auction.claimPending();
        assertEq(auction.pendingWithdrawal(address(hostileSeller)), 0, "native hostile-bond: pending cleared");
        assertEq(address(hostileSeller).balance - balBefore, parked, "native hostile-bond: full amount recovered");
    }

    /// @dev ERC-20 rail: the payment token's transfer returns false, so the WINNER's escrow + bond
    ///      pushes are parked. The winner is a normal EOA (seller, opener, ReleaseToSeller wins).
    function _hostileBondWinnerToken() private {
        E_FalseReturningERC20 badToken = new E_FalseReturningERC20();
        SessionAuction a = _disputedOnToken(badToken, ESCROW_E, seller); // seller opens; seller WINS release

        uint256 fee = Math.mulDiv(ESCROW_E, FEE_BPS, 10_000);
        uint256 proceeds = ESCROW_E - fee;
        // seller is the bond winner AND the proceeds payee; feeRecipient also takes fee on this token.
        uint256 parked = proceeds + uint256(DISPUTE_BOND_AMT);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalCredited(seller, uint256(DISPUTE_BOND_AMT));

        vm.prank(arbiter);
        a.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, ARB_PHOTO);

        Lot memory lot = a.getLot(LOT_ID);
        assertEq(uint256(lot.disputeBond), 0, "token hostile-bond: bond zeroed");
        assertEq(uint256(lot.escrowAmount), 0, "token hostile-bond: escrow zeroed");
        assertEq(uint8(lot.phase), uint8(LotPhase.Settled), "token hostile-bond: resolution completed (Settled)");
        assertEq(a.pendingWithdrawal(seller), parked, "token hostile-bond: proceeds + bond parked, no strand");

        // recoverable: heal the token, claimPending pulls the parked proceeds + bond to the seller.
        badToken.setFail(false);
        uint256 balBefore = badToken.balanceOf(seller);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(seller, parked);
        vm.prank(seller);
        a.claimPending();
        assertEq(a.pendingWithdrawal(seller), 0, "token hostile-bond: pending cleared");
        assertEq(badToken.balanceOf(seller) - balBefore, parked, "token hostile-bond: full amount recovered");
    }

    // Private pre-state + assertion helpers.

    /// @dev Initialize the session clone with a payment token (native if address(0)) and open LOT_ID.
    function _initSession(address payToken) private {
        InitConfig memory cfg = _defaultInitConfig(payToken);
        _initWithConfig(cfg);
    }

    function _initWithConfig(InitConfig memory cfg) private {
        auction.initialize(cfg);

        // register the operator key that the test fixtures attest under.
        vm.prank(address(hammer));
        auction.registerOperatorKey(opQxBase, opQyBase);

        // open LOT_ID via the hammer (onlyHammer); endsAt one hour out.
        vm.prank(address(hammer));
        auction.openLot(LOT_ID, seller, RESERVE_PRICE, uint64(block.timestamp + 1 hours));
    }

    /// @dev Fund the winning bidder for `escrow` on the chosen rail and place a single winning bid.
    ///      The bidder commits `escrow` as their ceiling deposit and bids `escrow` (>= reserve), so
    ///      hammer snapshots escrowAmount == escrow into the lot.
    function _placeWinningBid(address payToken, uint128 escrow) private {
        // deposit the ceiling (native sends value; ERC-20 approves then deposits).
        if (payToken == address(0)) {
            vm.deal(bidder1, uint256(escrow) + 1 ether);
            vm.prank(bidder1);
            auction.depositCeiling{value: escrow}(LOT_ID, escrow);
        } else {
            token.mint(bidder1, uint256(escrow));
            vm.prank(bidder1);
            token.approve(address(auction), escrow);
            vm.prank(bidder1);
            auction.depositCeiling(LOT_ID, escrow);
        }

        // land bidder1 as the top with committed == escrow. These tests only need a finalized winner;
        // full attestation correctness is covered by the bid-path tests.
        _landTopBid(bidder1, escrow);
    }

    /// @dev Minimal winning-bid placement: land bidder1 as the recorded winner. Built against the exact
    ///      placeBid signature so it binds to the frozen surface.
    function _landTopBid(address principal, uint128 amount) private {
        _landTopBidOn(auction, principal, amount);
    }

    /// @dev Drive LOT_ID to LotPhase.Awaiting / DeliveryState.AwaitingDelivery carrying escrow == E.
    ///      Path: initialize -> openLot -> depositCeiling -> placeBid -> hammer -> finalizeWinner.
    function _driveToAwaiting(address payToken, uint128 escrow) private {
        _initSession(payToken);
        _placeWinningBid(payToken, escrow);

        // close the auction and hammer (Open -> Hammered, snapshots escrowAmount).
        vm.warp(block.timestamp + 2 hours); // past endsAt
        auction.hammer(LOT_ID);

        // reveal the winning bid so the reveal gate is satisfied for finalize.
        uint64 wseq = auction.getLot(LOT_ID).winnerSeq;
        vm.prank(bidder1);
        auction.reveal(LOT_ID, wseq, escrow, bytes32("salt"));

        // close the anti-collusion window, then finalize (Hammered -> Awaiting).
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        auction.finalizeWinner(LOT_ID);
    }

    /// @dev Same as _driveToAwaiting but the session was already initialized via _initWithConfig
    ///      (used by the zero-fee test which needs a custom InitConfig).
    function _driveToDeliveredPreInitialized(uint128 escrow) private {
        _placeWinningBid(address(0), escrow);

        vm.warp(block.timestamp + 2 hours);
        auction.hammer(LOT_ID);

        uint64 wseq = auction.getLot(LOT_ID).winnerSeq;
        vm.prank(bidder1);
        auction.reveal(LOT_ID, wseq, escrow, bytes32("salt"));

        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        auction.finalizeWinner(LOT_ID);

        vm.prank(seller);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);
    }

    /// @dev Drive LOT_ID to DeliveryState.Delivered (seller has marked delivered).
    function _driveToDelivered(address payToken, uint128 escrow) private {
        _driveToAwaiting(payToken, escrow);
        vm.prank(seller);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);
    }

    /// @dev Drive LOT_ID to Delivered with a winning bid that landed over its committed ceiling (bid
    ///      amount ESCROW_E > committed E_OVER_MAXBID). escrowAmount still snapshots the BID amount
    ///      (escrowAmount = highBid), so the fee/release math matches _driveToDelivered. The reveal opens
    ///      with the true (E_OVER_MAXBID, E_OVER_SALT) pair (reveal only checks that the commit opens).
    ///      This makes a subsequent challengeOverCeiling a valid over-ceiling claim (commit matches AND
    ///      amount > maxBid). Native rail.
    function _driveToDeliveredOverCeiling(uint128 escrow) private {
        _initSession(address(0));

        // deposit the ceiling and land the OVER-ceiling top bid (commit's maxBid < bid amount).
        vm.deal(bidder1, uint256(escrow) + 1 ether);
        vm.prank(bidder1);
        auction.depositCeiling{value: escrow}(LOT_ID, escrow);
        _landTopBidOnWithCommit(auction, bidder1, escrow, E_OVER_MAXBID, E_OVER_SALT);

        vm.warp(block.timestamp + 2 hours); // past endsAt
        auction.hammer(LOT_ID);

        // reveal with the TRUE committed opening (E_OVER_MAXBID, E_OVER_SALT), NOT the bid amount.
        uint64 wseq = auction.getLot(LOT_ID).winnerSeq;
        vm.prank(bidder1);
        auction.reveal(LOT_ID, wseq, E_OVER_MAXBID, E_OVER_SALT);

        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        auction.finalizeWinner(LOT_ID);

        vm.prank(seller);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);
    }

    /// @dev Drive LOT_ID to DeliveryState.Disputed with `opener` (buyer or seller) holding the bond.
    function _driveToDisputed(address payToken, uint128 escrow, address opener) private {
        _driveToAwaiting(payToken, escrow);
        _openDisputeAs(payToken, opener, CLAIM_REF);
    }

    /// @dev Drive a SECOND lot (`lot2Id`, e.g. 2) to DeliveryState.Disputed on the ALREADY-initialized
    ///      native session (does NOT re-initialize, which would revert InvalidInitialization). The seller
    ///      and arbiter are the session defaults; the buyer/opener is bidder1. Used by the cross-lot
    ///      isolation test (resolving LOT_ID must not touch this lot). Native rail only.
    function _driveSecondLotToDisputed(uint256 lot2Id, uint128 escrow, address opener) private {
        // open the second lot via the hammer (the session is already initialized for LOT_ID).
        vm.prank(address(hammer));
        auction.openLot(lot2Id, seller, RESERVE_PRICE, uint64(block.timestamp + 1 hours));

        // bidder1 deposits + lands the winning bid on lot 2 (deposits are per-lot keyed).
        vm.deal(bidder1, uint256(escrow) + 1 ether);
        vm.prank(bidder1);
        auction.depositCeiling{value: escrow}(lot2Id, escrow);
        _landTopBidOnLot(lot2Id, bidder1, escrow);

        vm.warp(block.timestamp + 2 hours); // past lot 2 endsAt
        auction.hammer(lot2Id);

        uint64 wseq2 = auction.getLot(lot2Id).winnerSeq;
        vm.prank(bidder1);
        auction.reveal(lot2Id, wseq2, escrow, bytes32("salt"));

        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        auction.finalizeWinner(lot2Id);

        // open the dispute on lot 2 with the native bond.
        vm.deal(opener, opener.balance + uint256(DISPUTE_BOND_AMT));
        vm.prank(opener);
        auction.openDispute{value: DISPUTE_BOND_AMT}(lot2Id, CLAIM_REF);
    }

    /// @dev Open a dispute as `opener`, posting the bond on the correct rail (native value vs ERC-20
    ///      approve + zero msg.value). Binds to the exact openDispute signature.
    function _openDisputeAs(address payToken, address opener, bytes32 claimRef) private {
        if (payToken == address(0)) {
            vm.deal(opener, opener.balance + uint256(DISPUTE_BOND_AMT));
            vm.prank(opener);
            auction.openDispute{value: DISPUTE_BOND_AMT}(LOT_ID, claimRef);
        } else {
            token.mint(opener, uint256(DISPUTE_BOND_AMT));
            vm.prank(opener);
            token.approve(address(auction), DISPUTE_BOND_AMT);
            vm.prank(opener);
            auction.openDispute(LOT_ID, claimRef);
        }
    }

    /// @dev Open a Class B bid-integrity dispute on the winning seq (sets bidIntegrityOpen, the gate
    ///      that blocks _release). Posts _integrityBondAmt on the native rail.
    function _openClassBIntegrityDispute() private {
        uint64 seq = auction.getLot(LOT_ID).winnerSeq;
        vm.deal(bidder2, bidder2.balance + uint256(INTEGRITY_BOND_AMT));
        vm.prank(bidder2);
        auction.challengeAttestation{value: INTEGRITY_BOND_AMT}(LOT_ID, seq, hex"deadbeef");
    }

    /// @dev Open a Class A over-ceiling challenge on the winning seq (self-proving, never gates
    ///      _release). The principal (bidder1) proves it by opening the commitment with the true
    ///      (maxBid, salt). Requires a winner driven via _driveToDeliveredOverCeiling, whose commit
    ///      binds E_OVER_MAXBID (< ESCROW_E) so both checks pass: keccak256(abi.encode(maxBid, salt)) ==
    ///      storedCommit (no CommitmentMismatch) AND amount > maxBid (no NotOverCeiling). An at-ceiling
    ///      commit cannot open a valid Class A (its maxBid equals the bid amount).
    function _openClassAOverCeiling() private {
        uint64 seq = auction.getLot(LOT_ID).winnerSeq;
        vm.prank(bidder1);
        auction.challengeOverCeiling(LOT_ID, seq, E_OVER_MAXBID, E_OVER_SALT);
    }

    // Additional pre-state drivers.

    /// @dev Drive LOT_ID to Hammered + revealed + AC window closed, stopping before finalizeWinner so
    ///      a test can assert the entry transition (WinnerFinalized + post-state) on finalize itself.
    function _driveToHammeredRevealed(address payToken, uint128 escrow) private {
        _initSession(payToken);
        _placeWinningBid(payToken, escrow);
        vm.warp(block.timestamp + 2 hours); // past endsAt
        auction.hammer(LOT_ID);
        uint64 wseq = auction.getLot(LOT_ID).winnerSeq;
        vm.prank(bidder1);
        auction.reveal(LOT_ID, wseq, escrow, bytes32("salt"));
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1); // AC window closed; finalize is now legal
    }

    /// @dev Drive LOT_ID to DeliveryState.Disputed, optionally PASSING THROUGH Delivered first so the
    ///      dispute carries a nonzero deliveredAt anchor (the Delivered-origin {.,Delivered}->Disputed
    ///      edge). Native rail.
    function _driveToDisputedFrom(address payToken, uint128 escrow, address opener, bool viaDelivered) private {
        _driveToAwaiting(payToken, escrow);
        if (viaDelivered) {
            vm.prank(seller);
            auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);
        }
        _openDisputeAs(payToken, opener, CLAIM_REF);
    }

    /// @dev Drive LOT_ID to Delivered with a CUSTOM reserve (so sub-reserve fee witnesses can clear
    ///      hammer). Native rail. Mirrors _driveToAwaiting but opens the lot at `reserve`.
    function _driveToDeliveredWithReserve(address payToken, uint128 escrow, uint96 reserve) private {
        InitConfig memory cfg = _defaultInitConfig(payToken);
        auction.initialize(cfg);
        vm.prank(address(hammer));
        auction.registerOperatorKey(opQxBase, opQyBase);
        vm.prank(address(hammer));
        auction.openLot(LOT_ID, seller, reserve, uint64(block.timestamp + 1 hours));

        _placeWinningBid(payToken, escrow);
        vm.warp(block.timestamp + 2 hours);
        auction.hammer(LOT_ID);
        // hoist winnerSeq before the prank: an inline getLot(...) consumes the prank, so reveal would
        // run unpranked and revert NotPrincipal.
        uint64 wseq = auction.getLot(LOT_ID).winnerSeq;
        vm.prank(bidder1);
        auction.reveal(LOT_ID, wseq, escrow, bytes32("salt"));
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        auction.finalizeWinner(LOT_ID);
        vm.prank(seller);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);
    }

    /// @dev Native lot driven to Delivered with a CUSTOM buyer and CUSTOM seller (used to install a
    ///      reentrant contract on either side). The buyer is the recorded principal (depositor +
    ///      revealer); the seller is set via openLot.
    function _driveToDeliveredWith(uint128 escrow, address buyer, address sellerAddr) private {
        _initOn(auction, address(0));
        vm.prank(address(hammer));
        auction.openLot(LOT_ID, sellerAddr, RESERVE_PRICE, uint64(block.timestamp + 1 hours));

        vm.deal(buyer, uint256(escrow) + 1 ether);
        vm.prank(buyer);
        auction.depositCeiling{value: escrow}(LOT_ID, escrow);
        _landTopBidOn(auction, buyer, escrow);

        vm.warp(block.timestamp + 2 hours);
        auction.hammer(LOT_ID);
        // hoist winnerSeq before the prank (an inline getLot consumes it -> reveal unpranked -> NotPrincipal).
        uint64 wseq = auction.getLot(LOT_ID).winnerSeq;
        vm.prank(buyer);
        auction.reveal(LOT_ID, wseq, escrow, bytes32("salt"));
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        auction.finalizeWinner(LOT_ID);
        vm.prank(sellerAddr);
        auction.markDelivered(LOT_ID, PROOF_HASH, DELIVERY_CID);
    }

    /// @dev Native Disputed lot whose SELLER (and dispute opener) is `sellerAddr` (a contract or EOA),
    ///      with the EOA buyer bidder1 placing the bid (no ERC-1271 needed for a contract seller). The
    ///      seller posts the native bond.
    function _driveToDisputedWithSeller(uint128 escrow, address sellerAddr) private {
        _initOn(auction, address(0));
        vm.prank(address(hammer));
        auction.openLot(LOT_ID, sellerAddr, RESERVE_PRICE, uint64(block.timestamp + 1 hours));

        vm.deal(bidder1, uint256(escrow) + 1 ether);
        vm.prank(bidder1);
        auction.depositCeiling{value: escrow}(LOT_ID, escrow);
        _landTopBidOn(auction, bidder1, escrow);

        vm.warp(block.timestamp + 2 hours);
        auction.hammer(LOT_ID);
        // hoist winnerSeq before the prank (an inline getLot consumes it -> reveal unpranked -> NotPrincipal).
        uint64 wseq = auction.getLot(LOT_ID).winnerSeq;
        vm.prank(bidder1);
        auction.reveal(LOT_ID, wseq, escrow, bytes32("salt"));
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        auction.finalizeWinner(LOT_ID);

        // the seller opens the dispute with the native bond.
        vm.deal(sellerAddr, sellerAddr.balance + uint256(DISPUTE_BOND_AMT));
        vm.prank(sellerAddr);
        auction.openDispute{value: DISPUTE_BOND_AMT}(LOT_ID, CLAIM_REF);
    }

    /// @dev Native lot driven to AwaitingDelivery (NOT marked delivered) with a CUSTOM buyer and CUSTOM
    ///      seller (mirror of _driveToDeliveredWith that stops before markDelivered, for the buyer-side
    ///      reclaimUndelivered reentrancy test). The buyer is the recorded principal; the seller is set
    ///      via openLot.
    function _driveToAwaitingWith(uint128 escrow, address buyer, address sellerAddr) private {
        _initOn(auction, address(0));
        vm.prank(address(hammer));
        auction.openLot(LOT_ID, sellerAddr, RESERVE_PRICE, uint64(block.timestamp + 1 hours));

        // the buyer is an ERC-1271 contract whose owner is bidder1, so the bid envelope is signed with
        // bidder1Key (its isValidSignature recovers that signature to bidder1 and authorizes the bid).
        _bindContractSigner(buyer, bidder1Key);
        _mockPaddle(buyer, _paddleFor(buyer)); // contract principal still needs a nonzero KYC paddle

        vm.deal(buyer, uint256(escrow) + 1 ether);
        vm.prank(buyer);
        auction.depositCeiling{value: escrow}(LOT_ID, escrow);
        _landTopBidOn(auction, buyer, escrow);

        vm.warp(block.timestamp + 2 hours);
        auction.hammer(LOT_ID);
        uint64 wseq = auction.getLot(LOT_ID).winnerSeq;
        vm.prank(buyer);
        auction.reveal(LOT_ID, wseq, escrow, bytes32("salt"));
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        auction.finalizeWinner(LOT_ID); // rests in AwaitingDelivery (no markDelivered)
    }

    /// @dev Native Disputed lot whose BUYER (and dispute opener) is `buyerAddr` (a contract or EOA), with
    ///      the default EOA seller. Roles-swapped mirror of _driveToDisputedWithSeller: the buyer is the
    ///      recorded principal and posts the native bond, so on RefundToBuyer the opener wins and receives
    ///      escrow + bond. For the buyer-side resolveDispute(RefundToBuyer) reentrancy test.
    function _driveToDisputedWithBuyer(uint128 escrow, address buyerAddr) private {
        _initOn(auction, address(0));
        vm.prank(address(hammer));
        auction.openLot(LOT_ID, seller, RESERVE_PRICE, uint64(block.timestamp + 1 hours));

        // the buyer is an ERC-1271 contract whose owner is bidder1: sign the bid envelope with bidder1Key
        // (isValidSignature recovers it to bidder1) and give the contract principal a nonzero KYC paddle.
        _bindContractSigner(buyerAddr, bidder1Key);
        _mockPaddle(buyerAddr, _paddleFor(buyerAddr));

        vm.deal(buyerAddr, uint256(escrow) + 1 ether);
        vm.prank(buyerAddr);
        auction.depositCeiling{value: escrow}(LOT_ID, escrow);
        _landTopBidOn(auction, buyerAddr, escrow);

        vm.warp(block.timestamp + 2 hours);
        auction.hammer(LOT_ID);
        // hoist winnerSeq before the prank (an inline getLot consumes it -> reveal unpranked -> NotPrincipal).
        uint64 wseq = auction.getLot(LOT_ID).winnerSeq;
        vm.prank(buyerAddr);
        auction.reveal(LOT_ID, wseq, escrow, bytes32("salt"));
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        auction.finalizeWinner(LOT_ID);

        // the BUYER opens the dispute with the native bond (so the opener == buyer and wins RefundToBuyer).
        vm.deal(buyerAddr, buyerAddr.balance + uint256(DISPUTE_BOND_AMT));
        vm.prank(buyerAddr);
        auction.openDispute{value: DISPUTE_BOND_AMT}(LOT_ID, CLAIM_REF);
    }

    /// @dev Voided-and-promoted entry into the delivery lifecycle: a flagged offender (bidder2) is the
    ///      provisional top, bidder1 is the strictly-lower clean bid (escrow == E). voidAndAward promotes
    ///      bidder1, then finalizeWinner lands it in AwaitingDelivery at the same node as any winner. The
    ///      paddle/flag registries are mocked here; full attestation + multi-bid correctness is covered
    ///      by the void-path tests.
    function _driveToAwaitingViaVoid(uint128 escrow) private {
        _initOn(auction, address(0));

        vm.prank(address(hammer));
        auction.openLot(LOT_ID, seller, RESERVE_PRICE, uint64(block.timestamp + 1 hours));

        // mock KYC paddles: bidder1 CLEAN, bidder2 OFFENDER (both nonzero == registered).
        _mockPaddle(bidder1, E_PADDLE_CLEAN);
        _mockPaddle(bidder2, E_PADDLE_OFFENDER);

        // fund + deposit both: bidder1 commits E; bidder2 (offender) commits a strictly higher top.
        uint128 offenderBid = escrow + 10 ether;
        vm.deal(bidder1, uint256(escrow) + 1 ether);
        vm.prank(bidder1);
        auction.depositCeiling{value: escrow}(LOT_ID, escrow);
        vm.deal(bidder2, uint256(offenderBid) + 1 ether);
        vm.prank(bidder2);
        auction.depositCeiling{value: offenderBid}(LOT_ID, offenderBid);

        // ascending bids: bidder1 (clean, seq 1) then bidder2 (offender top, seq 2).
        _landTopBidOn(auction, bidder1, escrow);
        _landTopBidOn(auction, bidder2, offenderBid);

        vm.warp(block.timestamp + 2 hours);
        auction.hammer(LOT_ID); // offender (bidder2) is the provisional winner; escrow == offenderBid

        // mock the flag tree: offender FLAGGED (membership true), clean candidate UNFLAGGED.
        _mockFlagsHappyVoid();

        // promote the clean candidate (bidder1) at heapIndex 0; one strictly-higher slot (offender).
        bytes32[][] memory preceding = new bytes32[][](1);
        preceding[0] = _flaggedProofVoid(E_PADDLE_OFFENDER);
        NextCleanCandidate memory cand = NextCleanCandidate({
            heapIndex: 0,
            bidder: bidder1,
            amount: escrow,
            paddleId: E_PADDLE_CLEAN,
            seq: uint40(1),
            flagNonMembership: _nonMembershipProofVoid(E_PADDLE_CLEAN),
            precedingFlagInclusion: preceding
        });
        auction.voidAndAward(LOT_ID, _flaggedProofVoid(E_PADDLE_OFFENDER), cand);

        // close the (FROZEN voidedAt-anchored) AC window, reveal the promoted seq, finalize -> Awaiting.
        uint64 wseq = auction.getLot(LOT_ID).winnerSeq;
        vm.prank(bidder1);
        auction.reveal(LOT_ID, wseq, escrow, bytes32("salt"));
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        auction.finalizeWinner(LOT_ID);
    }

    /// @dev Fresh clone on a CUSTOM ERC-20 rail (e.g. a reentrant/false-returning token), driven to
    ///      AwaitingDelivery with `buyer` as the recorded principal. Returns the clone.
    function _awaitingOnToken(MockERC20 payToken, uint128 escrow, address buyer) private returns (SessionAuction a) {
        a = SessionAuction(Clones.clone(address(impl)));
        _initOn(a, address(payToken));
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, uint64(block.timestamp + 1 hours));

        payToken.mint(buyer, uint256(escrow));
        vm.prank(buyer);
        payToken.approve(address(a), escrow);
        vm.prank(buyer);
        a.depositCeiling(LOT_ID, escrow); // ERC-20: msg.value == 0
        _landTopBidOn(a, buyer, escrow);

        vm.warp(block.timestamp + 2 hours);
        a.hammer(LOT_ID);
        uint64 wseq = a.getLot(LOT_ID).winnerSeq;
        vm.prank(buyer);
        a.reveal(LOT_ID, wseq, escrow, bytes32("salt"));
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        a.finalizeWinner(LOT_ID);
    }

    /// @dev Fresh clone on a CUSTOM ERC-20 rail driven to Disputed, with `opener` posting the token
    ///      bond. Returns the clone. Used for the hostile-bond (false-returning token) resolution.
    function _disputedOnToken(MockERC20 payToken, uint128 escrow, address opener) private returns (SessionAuction a) {
        a = _awaitingOnToken(payToken, escrow, bidder1); // buyer == bidder1
        payToken.mint(opener, uint256(DISPUTE_BOND_AMT));
        vm.prank(opener);
        payToken.approve(address(a), DISPUTE_BOND_AMT);
        vm.prank(opener);
        a.openDispute(LOT_ID, CLAIM_REF); // ERC-20 bond: msg.value == 0
    }

    // Shared low-level build primitives.

    /// @dev Initialize `a` for `payTokenAddr` and seed the operator key (onlyHammer).
    function _initOn(SessionAuction a, address payTokenAddr) private {
        a.initialize(_defaultInitConfig(payTokenAddr));
        vm.prank(address(hammer));
        a.registerOperatorKey(opQxBase, opQyBase);
    }

    /// @dev Land `principal` as the top bid on clone `a` for `amount` (parameterized twin of
    ///      _landTopBid). Minimal valid bid envelope; full attestation correctness is covered by the
    ///      bid-path tests.
    function _landTopBidOn(SessionAuction a, address principal, uint128 amount) private {
        Ceiling memory c = Ceiling({
            principal: principal,
            sessionId: SESSION_ID,
            lotId: LOT_ID,
            ceilingCommit: keccak256(abi.encode(amount, bytes32("salt"))),
            strategy: 0,
            deadline: uint64(block.timestamp + 1 hours),
            maxBids: 16,
            nonceKey: uint192(uint256(keccak256(abi.encode(SESSION_ID, LOT_ID, principal))))
        });
        // real ceiling signature recovered to `principal` (a fake sig reverts BadSignature).
        // observedPrevTop must equal the live lot.highBid (else StalePrevTop), so read it rather than
        // hardcoding 0. bidIndex 0: each principal places one bid under its keyed nonce.
        uint128 prevTop = uint128(a.getLot(LOT_ID).highBid);
        bytes memory sig = _signCeiling(address(a), c, _signerKeyFor(principal));
        AttestationQuote memory q = _realQuote(c, LOT_ID, amount, 0, prevTop, keccak256(abi.encode(principal, amount)));
        // KYC gate: paddleOf(principal) must be nonzero (else Unauthorized). The void path mocks distinct
        // offender/clean paddles itself; here mock a stable nonzero paddle.
        _mockPaddleIfUnset(principal);
        vm.prank(principal);
        a.placeBid(c, LOT_ID, principal, 0, amount, sig, _baseOperatorKeyId(), q);
    }

    /// @dev Land `principal` as the top bid for `amount` while committing a ceiling of (`maxBid`, salt)
    ///      independent of `amount` (twin of _landTopBidOn, which forces the commit's maxBid == `amount`).
    ///      placeBid does NOT enforce the hidden maxBid (the operator may over-bid the cap, which is what
    ///      challengeOverCeiling later proves), so amount > maxBid is placeable and the opaque
    ///      ceilingCommit verifies identically. Builds an over-ceiling winner whose true (maxBid, salt)
    ///      opens cleanly and clears the amount > maxBid over-ceiling check.
    function _landTopBidOnWithCommit(SessionAuction a, address principal, uint128 amount, uint128 maxBid, bytes32 salt)
        private
    {
        Ceiling memory c = Ceiling({
            principal: principal,
            sessionId: SESSION_ID,
            lotId: LOT_ID,
            ceilingCommit: keccak256(abi.encode(maxBid, salt)),
            strategy: 0,
            deadline: uint64(block.timestamp + 1 hours),
            maxBids: 16,
            nonceKey: uint192(uint256(keccak256(abi.encode(SESSION_ID, LOT_ID, principal))))
        });
        uint128 prevTop = uint128(a.getLot(LOT_ID).highBid);
        bytes memory sig = _signCeiling(address(a), c, _signerKeyFor(principal));
        AttestationQuote memory q = _realQuote(c, LOT_ID, amount, 0, prevTop, keccak256(abi.encode(principal, amount)));
        _mockPaddleIfUnset(principal);
        vm.prank(principal);
        a.placeBid(c, LOT_ID, principal, 0, amount, sig, _baseOperatorKeyId(), q);
    }

    /// @dev Land `principal` as the top bid for `amount` on an arbitrary `lotId` of the shared `auction`
    ///      (lotId-parameterized twin of _landTopBid). Drives a second lot for the cross-lot isolation
    ///      test. Minimal valid bid envelope; full attestation correctness is covered by the bid-path
    ///      tests.
    function _landTopBidOnLot(uint256 lotId, address principal, uint128 amount) private {
        Ceiling memory c = Ceiling({
            principal: principal,
            sessionId: SESSION_ID,
            lotId: lotId,
            ceilingCommit: keccak256(abi.encode(amount, bytes32("salt"))),
            strategy: 0,
            deadline: uint64(block.timestamp + 1 hours),
            maxBids: 16,
            nonceKey: uint192(uint256(keccak256(abi.encode(SESSION_ID, lotId, principal))))
        });
        // real ceiling signature recovered to `principal`; observedPrevTop == this lot's live highBid.
        // bidIndex 0: first bid under (principal, key) for `lotId` (the keyed nonce is per-lot via the
        // lotId-derived nonceKey).
        uint128 prevTop = uint128(auction.getLot(lotId).highBid);
        bytes memory sig = _signCeiling(address(auction), c, _signerKeyFor(principal));
        AttestationQuote memory q =
            _realQuote(c, lotId, amount, 0, prevTop, keccak256(abi.encode(principal, amount, lotId)));
        _mockPaddleIfUnset(principal);
        vm.prank(principal);
        auction.placeBid(c, lotId, principal, 0, amount, sig, _baseOperatorKeyId(), q);
    }

    // Void-path paddle / flag mocks.

    // Tracks principals whose KYC paddle has been mocked explicitly (e.g. the void path's distinct
    // offender/clean paddles) so _landTopBidOn does not clobber them with its generic nonzero default.
    mapping(address => bool) private _paddleExplicitlySet;

    function _mockPaddle(address principal, uint16 paddleId) private {
        vm.mockCall(
            address(paddles), abi.encodeWithSelector(IPaddleRegistry.paddleOf.selector, principal), abi.encode(paddleId)
        );
        _paddleExplicitlySet[principal] = true;
    }

    /// @dev Mock a stable nonzero KYC paddle for `principal` (so placeBid sees paddleId != 0, not
    ///      Unauthorized) unless a test set one explicitly (the void path installs offender/clean paddles
    ///      first). Only != 0 matters to the bid path; the value is per-principal so the recorded paddleId
    ///      reflects the real bidder.
    function _mockPaddleIfUnset(address principal) private {
        if (_paddleExplicitlySet[principal]) return;
        vm.mockCall(
            address(paddles),
            abi.encodeWithSelector(IPaddleRegistry.paddleOf.selector, principal),
            abi.encode(_paddleFor(principal))
        );
    }

    /// @dev A stable DISTINCT nonzero paddle for `principal`: fold the address into [0x8000, 0xFFFF] so it
    ///      is never the unregistered sentinel 0 for any principal.
    function _paddleFor(address principal) private pure returns (uint16) {
        return uint16(uint256(uint160(principal)) & 0x7FFF) | 0x8000;
    }

    function _mockFlagsHappyVoid() private {
        vm.mockCall(address(flags), abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector), abi.encode(true));
        vm.mockCall(
            address(flags), abi.encodeWithSelector(IFlagRegistry.verifyNonMembership.selector), abi.encode(true)
        );
        // the offender paddle is FLAGGED: it must NOT satisfy non-membership.
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyNonMembership.selector, SESSION_ID, E_PADDLE_OFFENDER),
            abi.encode(false)
        );
        // the clean candidate is UNFLAGGED: it must NOT satisfy membership.
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector, SESSION_ID, E_PADDLE_CLEAN),
            abi.encode(false)
        );
    }

    function _flaggedProofVoid(uint16 paddle) private pure returns (bytes32[] memory proof) {
        proof = new bytes32[](3);
        proof[0] = bytes32(uint256(paddle)); // low == paddle (membership)
        proof[1] = bytes32(uint256(paddle) + 1); // high
        proof[2] = keccak256(abi.encode("sibling"));
    }

    function _nonMembershipProofVoid(uint16 paddle) private pure returns (bytes32[] memory proof) {
        proof = new bytes32[](3);
        proof[0] = bytes32(uint256(paddle) - 1); // low < paddle
        proof[1] = bytes32(uint256(paddle) + 1); // high > paddle (brackets it)
        proof[2] = keccak256(abi.encode("sibling"));
    }

    // Balance / escrow readers.

    /// @dev Single-account balance on the chosen rail.
    function _bal(address payToken, address who) private view returns (uint256) {
        return payToken == address(0) ? who.balance : token.balanceOf(who);
    }

    /// @dev Two-account balances on the chosen rail (gas-light tuple read).
    function _balances(address payToken, address a, address b) private view returns (uint256, uint256) {
        return (_bal(payToken, a), _bal(payToken, b));
    }

    /// @dev Total value held by the auction contract on the chosen rail (escrow + any bond pool).
    function _heldEscrow(address payToken) private view returns (uint256) {
        return payToken == address(0) ? address(auction).balance : token.balanceOf(address(auction));
    }
}
