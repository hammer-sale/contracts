// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Access control and pause across SessionAuction, Treasury, and OperatorBond.
//
// Covers: every role-gated SessionAuction function reverts Unauthorized for the wrong caller
// (onlyHammer / onlyPauser / onlySettler / onlyArbiter / onlySeller / onlyBuyer); pause scope
// (the whenNotPaused entrypoints revert EnforcedPause while refund / withdraw / settlement exits
// stay reachable); pause / unpause are onlyPauser and toggle Pausable state; and the auxiliary
// Treasury / OperatorBond gates reject the wrong caller while onlyAuction admits a registered clone.
//
// Negative assertions match a specific selector (Unauthorized / EnforcedPause), never a bare
// expectRevert, so an unrelated revert on the same call cannot false-pass.
//
// The only whenNotPaused entrypoints are placeBid and voidAndAward, both
// `external nonReentrant whenNotPaused`. nonReentrant (listed first) does not revert on a clean
// first entry, so whenNotPaused fires before any body guard. depositCeiling is `external payable`
// with no whenNotPaused, so it stays reachable under pause.
//
// initialize is not swept here: it is gated by the OZ `initializer` modifier (single-shot,
// reverting InvalidInitialization), not by a role. test_InitializeNotGatedByHammerRole pins that
// a non-hammer caller can initialize a fresh clone.

import {HammerBase} from "./HammerBase.t.sol";

import {Hammer}          from "../src/Hammer.sol";
import {SessionAuction}  from "../src/SessionAuction.sol";
import {ISessionAuction} from "../src/interfaces/ISessionAuction.sol";
import {ITreasury}       from "../src/interfaces/ITreasury.sol";
import {IOperatorBond}   from "../src/interfaces/IAgentBond.sol";

import {Pausable} from "@openzeppelin/contracts/utils/Pausable.sol";
import {Ownable}  from "@openzeppelin/contracts/access/Ownable.sol";
import {Clones}   from "@openzeppelin/contracts/proxy/Clones.sol";

import {Resolution, Ceiling, AttestationQuote, InitConfig, NextCleanCandidate} from "../src/types/HammerTypes.sol";

contract AccessControlTest is HammerBase {
    // Expected revert for every wrong-caller gate in this file. SessionAuction, Treasury, and
    // OperatorBond all declare Unauthorized(); a selector is a pure function of the signature string,
    // so this one value equals bytes4(keccak256("Unauthorized()")) for all three even though Treasury
    // and OperatorBond do not inherit ISessionAuction.
    bytes4 private immutable UNAUTHORIZED = ISessionAuction.Unauthorized.selector;

    // Lot id used by the onlySeller / onlyBuyer and pause-scope fixtures.
    uint256 private constant LOT_ID = 1;

    // Pre-state helpers. All go through the real factory entrypoint.

    /// @dev Clone initialized via the factory, so its roles (_hammer == address(hammer),
    ///      _settler, _arbiter, _pauser, ...) are the named actors from _defaultInitConfig.
    function _newSession(address paymentToken) private returns (SessionAuction a) {
        a = SessionAuction(hammer.createSession(_defaultInitConfig(paymentToken)));
    }

    /// @dev Native-rail clone with a single Open lot (seller == `seller`). openLot is onlyHammer,
    ///      so it is pranked as the factory address.
    function _sessionWithOpenLot() private returns (SessionAuction a) {
        a = _newSession(address(0));
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));
    }

    /// @dev Asserts the caller is NOT rejected by an Unauthorized gate. Used where the only pinnable
    ///      property is "passed the auth gate": the onlyAuction positive (a registered clone is
    ///      admitted) and the permissionless calls (disburse / settleSlash have no gate). A
    ///      non-reverting call satisfies it; any other revert (denomination / state / window) is
    ///      accepted, only Unauthorized fails. Callers MUST vm.prank first: this internal jump does
    ///      not consume the prank, so target.call is the next external call and inherits the pranked
    ///      msg.sender.
    function _assertNotUnauthorized(address target, bytes memory callData) private {
        (bool ok, bytes memory ret) = target.call(callData);

        if (ok) return;

        // A custom-error revert leads with its 4-byte selector; bytes4(ret) reads it.
        bytes4 got = ret.length >= 4 ? bytes4(ret) : bytes4(0);
        assertTrue(got != UNAUTHORIZED, "caller must not be rejected by an Unauthorized auth gate");
    }

    /// @dev Asserts registerClone does NOT silently succeed for a non-factory caller, which would let
    ///      an EOA add itself to the clone set and pass every onlyAuction gate. Pins only that the
    ///      call reverts with some selector (got != bytes4(0)); the selector is returned so a caller
    ///      can pin it further. Callers MUST vm.prank the intended (non-factory) caller first: this
    ///      internal jump does not consume the prank, so target.call is the next external call and
    ///      inherits the pranked sender.
    function _assertRegisterCloneRejected(address target, address claimed) private returns (bytes4 got) {
        (bool ok, bytes memory ret) = target.call(abi.encodeCall(ITreasury.registerClone, (claimed)));

        assertFalse(ok, "registerClone must not silently succeed for a non-factory caller");
        got = ret.length >= 4 ? bytes4(ret) : bytes4(0);
        assertTrue(got != bytes4(0), "registerClone revert must carry a selector");
    }

    // Role-gated functions revert Unauthorized for the wrong caller. Split per modifier family for
    // diagnostics; the aggregate sweep below covers them together.

    /// onlyHammer (openLot) reverts Unauthorized for a caller that is not the stored _hammer
    /// (the factory).
    function test_RevertWhen_OpenLotWrongCaller() public {
        SessionAuction a = _newSession(address(0));

        vm.prank(bidder1); // not address(hammer)
        vm.expectRevert(UNAUTHORIZED);
        a.openLot(LOT_ID, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));
    }

    function test_RevertWhen_RegisterOperatorKeyWrongCaller() public {
        SessionAuction a = _newSession(address(0));

        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.registerOperatorKey(keccak256("QX"), keccak256("QY"));
    }

    function test_RevertWhen_RevokeOperatorKeyWrongCaller() public {
        SessionAuction a = _newSession(address(0));

        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.revokeOperatorKey(keccak256(abi.encode(keccak256("QX"), keccak256("QY"))));
    }

    function test_RevertWhen_VoidSessionWrongCaller() public {
        SessionAuction a = _newSession(address(0));

        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.voidSession("collusion");
    }

    /// onlySettler (commitBidBook) reverts Unauthorized for a non-settler caller.
    function test_RevertWhen_CommitBidBookWrongCaller() public {
        SessionAuction a = _newSession(address(0));

        vm.prank(bidder1); // not `settler`
        vm.expectRevert(UNAUTHORIZED);
        a.commitBidBook(LOT_ID, keccak256("ROOT"));
    }

    /// onlyArbiter (resolveDispute) reverts Unauthorized for a non-arbiter caller.
    function test_RevertWhen_ResolveDisputeWrongCaller() public {
        SessionAuction a = _newSession(address(0));

        vm.prank(bidder1); // not `arbiter`
        vm.expectRevert(UNAUTHORIZED);
        a.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, keccak256("PHOTO"));
    }

    /// onlyArbiter (resolveBidIntegrityDispute) reverts Unauthorized for a non-arbiter caller.
    function test_RevertWhen_ResolveBidIntegrityDisputeWrongCaller() public {
        SessionAuction a = _newSession(address(0));

        vm.prank(bidder1); // not `arbiter`
        vm.expectRevert(UNAUTHORIZED);
        a.resolveBidIntegrityDispute(LOT_ID, 1, true, 0);
    }

    /// onlySeller (markDelivered) checks _lots[lotId].seller; a non-seller reverts Unauthorized,
    /// because the modifier runs before any state / timing check in the body.
    function test_RevertWhen_MarkDeliveredWrongCaller() public {
        SessionAuction a = _sessionWithOpenLot(); // seller stored == `seller`

        vm.prank(bidder1); // not the stored seller
        vm.expectRevert(UNAUTHORIZED);
        a.markDelivered(LOT_ID, keccak256("PROOF"), "ipfs://proof");
    }

    /// onlyBuyer (confirmReceipt) checks _lots[lotId].highBidder; a non-buyer reverts Unauthorized
    /// before any deliveryState check.
    function test_RevertWhen_ConfirmReceiptWrongCaller() public {
        SessionAuction a = _sessionWithOpenLot();

        vm.prank(seller); // the seller is not the buyer (highBidder)
        vm.expectRevert(UNAUTHORIZED);
        a.confirmReceipt(LOT_ID, keccak256("PHOTO"), "ipfs://photo");
    }

    /// onlyBuyer (reclaimUndelivered) checks _lots[lotId].highBidder; a non-buyer reverts Unauthorized.
    function test_RevertWhen_ReclaimUndeliveredWrongCaller() public {
        SessionAuction a = _sessionWithOpenLot();

        vm.prank(seller); // not the buyer (highBidder)
        vm.expectRevert(UNAUTHORIZED);
        a.reclaimUndelivered(LOT_ID);
    }

    /// Aggregate sweep: every SessionAuction role-gated entrypoint reverts Unauthorized when called
    /// without the role. The per-family tests above split this out for diagnostics.
    function test_RevertWhen_RoleGatedWrongCaller() public {
        SessionAuction a = _sessionWithOpenLot(); // seller stored; roles wired to named actors

        // onlyHammer (caller bidder1 != address(hammer))
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.openLot(2, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));

        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.registerOperatorKey(keccak256("QX2"), keccak256("QY2"));

        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.revokeOperatorKey(keccak256("KEYID"));

        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.voidSession("reason");

        // onlyPauser (caller bidder1 != `pauser`)
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.pause();

        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.unpause();

        // onlySettler (caller bidder1 != `settler`)
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.commitBidBook(LOT_ID, keccak256("ROOT"));

        // onlyArbiter (caller bidder1 != `arbiter`)
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.resolveDispute(LOT_ID, Resolution.RefundToBuyer, keccak256("PHOTO"));

        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.resolveBidIntegrityDispute(LOT_ID, 1, false, 0);

        // onlySeller (caller bidder1 != stored seller)
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.markDelivered(LOT_ID, keccak256("PROOF"), "ipfs://proof");

        // onlyBuyer (caller seller != stored highBidder)
        vm.prank(seller);
        vm.expectRevert(UNAUTHORIZED);
        a.confirmReceipt(LOT_ID, keccak256("PHOTO"), "ipfs://photo");

        vm.prank(seller);
        vm.expectRevert(UNAUTHORIZED);
        a.reclaimUndelivered(LOT_ID);
    }

    // Pause scope. The whenNotPaused entrypoints (placeBid, voidAndAward) revert EnforcedPause while
    // paused. The refund / withdraw / settlement exits carry no whenNotPaused and stay reachable,
    // reverting their own guard rather than EnforcedPause, so in-flight escrow can always resolve even
    // while the session is paused.
    //
    // For the escrow exits these tests assert only that the call reaches its own body guard while
    // paused (selector != EnforcedPause), not the money movement: reaching a real Delivered / Disputed
    // pre-state needs the bidding and attestation fixtures. The executes-while-paused positive lives
    // in E_DeliveryDisputes.t.sol (test_D5NotPausable, and test_IntegrityGateDoesNotBlockRefund for
    // the refund leg).

    /// Under pause, both whenNotPaused entrypoints (placeBid, voidAndAward) revert EnforcedPause,
    /// while every in-flight escrow exit (withdrawDeposit / withdrawRefund / claimPending /
    /// confirmReceipt / releaseAfterWindow / reclaimUndelivered / openDispute / resolveDispute) stays
    /// reachable and reverts its own body guard, never EnforcedPause. A stray whenNotPaused on any
    /// exit would surface here as EnforcedPause. Selector-reach only; the money movement is in
    /// E_DeliveryDisputes.t.sol test_D5NotPausable.
    function test_PauseScope() public {
        SessionAuction a = _sessionWithOpenLot();

        // Pause via the onlyPauser entrypoint. Expecting Paused(pauser) confirms the state went
        // through the real Pausable path (which emits Paused(_msgSender())), not a bare flag flip.
        vm.expectEmit(false, false, false, true, address(a));
        emit Pausable.Paused(pauser);
        vm.prank(pauser);
        a.pause();
        assertTrue(a.paused(), "clone should be paused");

        // placeBid (whenNotPaused) reverts EnforcedPause. Envelope and attestation are zero-valued;
        // nonReentrant does not revert on a first entry, so whenNotPaused fires before any validation.
        Ceiling memory c;
        AttestationQuote memory q;
        vm.prank(bidder1);
        vm.expectRevert(Pausable.EnforcedPause.selector);
        a.placeBid(c, LOT_ID, bidder1, 0, uint128(RESERVE_PRICE), "", bytes32(0), q);

        // voidAndAward (whenNotPaused) also reverts EnforcedPause before its body guards, so the
        // Open-lot fixture with empty proof and candidate suffices.
        bytes32[] memory emptyProof;
        NextCleanCandidate memory emptyCandidate;
        vm.prank(bidder1);
        vm.expectRevert(Pausable.EnforcedPause.selector);
        a.voidAndAward(LOT_ID, emptyProof, emptyCandidate);

        // claimPending: no whenNotPaused; with no failed-push credit the body reverts
        // NothingToWithdraw, not EnforcedPause.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        a.claimPending();

        // confirmReceipt: no whenNotPaused. Fixture highBidder == address(0), so onlyBuyer fires first
        // for a non-buyer caller -> Unauthorized (not EnforcedPause), reached while paused.
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.confirmReceipt(LOT_ID, keccak256("PHOTO"), "ipfs://photo");

        // reclaimUndelivered: no whenNotPaused. Same onlyBuyer-first ordering on the zero-highBidder
        // fixture -> Unauthorized while paused, never EnforcedPause.
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.reclaimUndelivered(LOT_ID);

        // openDispute (payable): no whenNotPaused. Pranked as the stored seller, so the buyer|seller
        // party check passes and the next guard is the state pre-check: an Open lot (deliveryState
        // None) reverts WrongDeliveryState while paused. value 0 so the bond pull is not the first
        // failure.
        vm.prank(seller);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        a.openDispute{value: 0}(LOT_ID, keccak256("REF"));

        // withdrawDeposit(0): no free balance, zero amount -> NothingToWithdraw, not EnforcedPause.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        a.withdrawDeposit(LOT_ID, 0);

        // withdrawRefund: session not voided and lot not terminal-refundable -> SessionIsVoided (the
        // guard fronting this pull exit), reached while paused, not EnforcedPause.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.SessionIsVoided.selector);
        a.withdrawRefund(LOT_ID);
    }

    /// Pause is reversible at the entrypoint: after unpause both whenNotPaused entrypoints become
    /// reachable again. This re-calls both from the same zero-valued fixtures and asserts the revert
    /// is each function's post-gate body guard, not EnforcedPause (placeBid -> Unauthorized,
    /// voidAndAward -> NotHammered on the still-Open lot), catching an impl that pauses but never
    /// actually un-gates.
    function test_PauseReversibilityReEnablesGatedSurface() public {
        SessionAuction a = _sessionWithOpenLot();

        // Phase 1: while paused, both whenNotPaused entrypoints revert EnforcedPause. The arming pause
        // emits Paused(pauser).
        vm.expectEmit(false, false, false, true, address(a));
        emit Pausable.Paused(pauser);
        vm.prank(pauser);
        a.pause();
        assertTrue(a.paused(), "clone should be paused");

        Ceiling memory c;          // zero struct: c.principal == address(0)
        AttestationQuote memory q;
        vm.prank(bidder1);
        vm.expectRevert(Pausable.EnforcedPause.selector);
        a.placeBid(c, LOT_ID, bidder1, 0, uint128(RESERVE_PRICE), "", bytes32(0), q);

        bytes32[] memory emptyProof;
        NextCleanCandidate memory emptyCandidate;
        vm.prank(bidder1);
        vm.expectRevert(Pausable.EnforcedPause.selector);
        a.voidAndAward(LOT_ID, emptyProof, emptyCandidate);

        // Phase 2: unpause via the onlyPauser entrypoint. Expecting Unpaused(pauser) confirms the
        // reversal went through the real Pausable._unpause path.
        vm.expectEmit(false, false, false, true, address(a));
        emit Pausable.Unpaused(pauser);
        vm.prank(pauser);
        a.unpause();
        assertFalse(a.paused(), "clone should be unpaused");

        // Phase 3: re-call both whenNotPaused entrypoints from the same zero-valued fixtures. The gate
        // no longer fronts either, so each reverts its post-gate body guard, never EnforcedPause.

        // placeBid: phase == Open passes, then the bid-authorization check c.principal (0) != principal
        // (bidder1) reverts Unauthorized.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        a.placeBid(c, LOT_ID, bidder1, 0, uint128(RESERVE_PRICE), "", bytes32(0), q);

        // voidAndAward: the phase == Hammered guard reverts NotHammered on the still-Open lot (same
        // guard as D_AntiCollusion test_RevertWhen_VoidNotHammered).
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.NotHammered.selector);
        a.voidAndAward(LOT_ID, emptyProof, emptyCandidate);
    }

    /// depositCeiling carries no whenNotPaused (it is `external payable`), so under pause it runs its
    /// body and reverts its denomination guard, not EnforcedPause. Native rail with
    /// msg.value != amount -> WrongDenomination.
    function test_DepositCeilingNotPauseGated() public {
        SessionAuction a = _sessionWithOpenLot(); // native rail (paymentToken == address(0))

        // Arming pause emits Paused(pauser).
        vm.expectEmit(false, false, false, true, address(a));
        emit Pausable.Paused(pauser);
        vm.prank(pauser);
        a.pause();

        // msg.value (0) != amount (RESERVE_PRICE) on the native rail -> WrongDenomination from _pull,
        // regardless of pause; never EnforcedPause (no whenNotPaused on depositCeiling).
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDenomination.selector);
        a.depositCeiling{value: 0}(LOT_ID, RESERVE_PRICE);
    }

    /// The settlement exits (releaseAfterWindow, resolveDispute) are timing / role gated, not pause
    /// gated, so on a paused lot each reverts its own guard, never EnforcedPause. A fresh Open lot
    /// (deliveryState None) makes the expected guards deterministic. The name's D5 tracks the same
    /// settlement-exit suite as E_DeliveryDisputes.t.sol test_D5NotPausable.
    function test_PauseDoesNotBlockD5Exits() public {
        SessionAuction a = _sessionWithOpenLot();

        // Arming pause emits Paused(pauser).
        vm.expectEmit(false, false, false, true, address(a));
        emit Pausable.Paused(pauser);
        vm.prank(pauser);
        a.pause();

        // releaseAfterWindow: permissionless, valid only from Delivered; a None/Open deliveryState
        // reverts WrongDeliveryState while paused, never EnforcedPause.
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        a.releaseAfterWindow(LOT_ID);

        // resolveDispute: onlyArbiter runs before the state guard, so a non-arbiter caller reverts
        // Unauthorized while paused, proving the arbiter settlement path is not pause gated.
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, keccak256("PHOTO"));
    }

    // pause / unpause are onlyPauser: a non-pauser reverts Unauthorized; the pauser toggles state.

    /// A non-pauser caller cannot pause or unpause (Unauthorized); the configured pauser toggles the
    /// Pausable state (paused() flips true then false). The toggles are wrapped in vm.expectEmit to
    /// pin Paused(pauser) / Unpaused(pauser): the events carry no indexed topic, so the mask
    /// (false, false, false, true) checks data + emitter only.
    function test_RevertWhen_PauseNotPauser() public {
        SessionAuction a = _newSession(address(0)); // _pauser == `pauser`

        // Non-pauser pause -> Unauthorized.
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.pause();

        // Non-pauser unpause -> Unauthorized.
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.unpause();

        // The configured pauser toggles state: pause flips paused() true and emits Paused(pauser).
        vm.expectEmit(false, false, false, true, address(a));
        emit Pausable.Paused(pauser);
        vm.prank(pauser);
        a.pause();
        assertTrue(a.paused(), "pauser should pause");

        // unpause flips it back to false and emits Unpaused(pauser) symmetrically.
        vm.expectEmit(false, false, false, true, address(a));
        emit Pausable.Unpaused(pauser);
        vm.prank(pauser);
        a.unpause();
        assertFalse(a.paused(), "pauser should unpause");
    }

    /// When cfg.pauser == address(0), initialize defaults the pause role to the hammer
    /// (_pauser = cfg.pauser == address(0) ? cfg.hammer : cfg.pauser). The other tests exercise the
    /// explicit branch (_defaultInitConfig wires a distinct pauser); this pins the fallback:
    /// address(hammer) toggles the Pausable state, and the named `pauser` is now rejected Unauthorized.
    function test_PauserDefaultsToHammer() public {
        InitConfig memory cfg = _defaultInitConfig(address(0));
        cfg.pauser = address(0); // no explicit pauser -> defaults to cfg.hammer (== address(hammer))
        SessionAuction a = SessionAuction(hammer.createSession(cfg));

        // The named `pauser` is not the default sink here, so it must not hold the role.
        vm.prank(pauser);
        vm.expectRevert(UNAUTHORIZED);
        a.pause();

        // The defaulted pauser (the hammer) toggles state. Checking Paused(address(hammer)) pins that
        // the defaulted _pauser is exactly the hammer, not just that some caller paused.
        vm.expectEmit(false, false, false, true, address(a));
        emit Pausable.Paused(address(hammer));
        vm.prank(address(hammer));
        a.pause();
        assertTrue(a.paused(), "hammer should be the default pauser");

        vm.expectEmit(false, false, false, true, address(a));
        emit Pausable.Unpaused(address(hammer));
        vm.prank(address(hammer));
        a.unpause();
        assertFalse(a.paused(), "hammer (default pauser) should unpause");
    }

    /// Pausable state-machine edges: pause() while already paused reverts EnforcedPause (via _pause's
    /// whenNotPaused); unpause() while not paused reverts ExpectedPause (via _unpause's whenPaused).
    /// Both run as the authorized pauser, so the revert is the state guard, not the onlyPauser gate.
    function test_PauseStateMachineEdges() public {
        SessionAuction a = _newSession(address(0)); // _pauser == `pauser`

        // Double-pause: first pause succeeds and emits Paused(pauser); a second pause (still pauser)
        // hits _pause's whenNotPaused -> EnforcedPause, not Unauthorized (the caller IS the pauser).
        // Only the succeeding first call is wrapped in expectEmit (the reverting call emits nothing).
        vm.expectEmit(false, false, false, true, address(a));
        emit Pausable.Paused(pauser);
        vm.prank(pauser);
        a.pause();
        assertTrue(a.paused(), "first pause should set paused");

        vm.prank(pauser);
        vm.expectRevert(Pausable.EnforcedPause.selector);
        a.pause();

        // Unpause-when-not-paused: unpause succeeds and emits Unpaused(pauser), then a second unpause
        // hits _unpause's whenPaused -> ExpectedPause (again the state guard, the caller IS the pauser).
        vm.expectEmit(false, false, false, true, address(a));
        emit Pausable.Unpaused(pauser);
        vm.prank(pauser);
        a.unpause();
        assertFalse(a.paused(), "unpause should clear paused");

        vm.prank(pauser);
        vm.expectRevert(Pausable.ExpectedPause.selector);
        a.unpause();
    }

    // Positive role authorization. The negative sweep proves the wrong caller is rejected; these
    // prove the correct stored-role principal is admitted past the gate, closing the "modifier wired
    // to the wrong slot, or rejects everyone" false-pass. Each pranks the stored role and asserts a
    // non-Unauthorized outcome: a pinned downstream state guard, a post-state change (pause toggle),
    // or the not-Unauthorized prover.

    /// onlyArbiter admits the stored arbiter: resolveDispute from `arbiter` passes onlyArbiter and
    /// then hits the state guard on an Open lot (deliveryState None, not Disputed) ->
    /// WrongDeliveryState, never Unauthorized.
    function test_ArbiterPassesGate() public {
        SessionAuction a = _sessionWithOpenLot();

        vm.prank(arbiter); // the stored _arbiter
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        a.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, keccak256("PHOTO"));
    }

    /// onlySeller admits the stored seller: markDelivered from the stored `seller` passes onlySeller
    /// and then hits the state guard on an Open lot (not Awaiting) -> WrongDeliveryState, never
    /// Unauthorized. Proves onlySeller keys to _lots[lotId].seller.
    function test_SellerPassesGate() public {
        SessionAuction a = _sessionWithOpenLot(); // seller stored == `seller`

        vm.prank(seller);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        a.markDelivered(LOT_ID, keccak256("PROOF"), "ipfs://proof");
    }

    /// onlyHammer admits the stored hammer: voidSession from address(hammer) passes onlyHammer and its
    /// body runs, emitting SessionVoided(SESSION_ID, "operator-panic"). Pinning the event (not just a
    /// non-reverting call) discriminates a modifier that admits the hammer but runs the wrong body, or
    /// one keyed off msg.sender rather than _hammer. sessionId is the lone indexed topic, so the mask
    /// checks topic1 + data.
    function test_HammerPassesGate() public {
        SessionAuction a = _newSession(address(0));

        vm.expectEmit(true, false, false, true, address(a));
        emit ISessionAuction.SessionVoided(SESSION_ID, "operator-panic");
        vm.prank(address(hammer)); // the stored _hammer
        a.voidSession("operator-panic");
    }

    /// onlySettler admits the stored settler: commitBidBook from `settler` passes onlySettler. No
    /// downstream guard selector is pinned for commitBidBook, so the not-Unauthorized prover is used.
    function test_SettlerPassesGate() public {
        SessionAuction a = _sessionWithOpenLot();

        vm.prank(settler); // the stored _settler
        _assertNotUnauthorized(
            address(a),
            abi.encodeCall(ISessionAuction.commitBidBook, (LOT_ID, keccak256("ROOT")))
        );
    }

    /// onlyBuyer with a zero stored highBidder (the _sessionWithOpenLot fixture has no bid, so
    /// lot.highBidder == address(0)): a caller of address(0) satisfies msg.sender == highBidder == 0
    /// and passes onlyBuyer, yet the downstream state guard reverts WrongDeliveryState on the Open lot
    /// rather than silently releasing escrow to address(0); a non-buyer (bidder1) is rejected
    /// Unauthorized. The winner-present positive for onlyBuyer / onlySeller lives in the delivery and
    /// bidding suites.
    function test_BuyerGateWithZeroHighBidder() public {
        SessionAuction a = _sessionWithOpenLot(); // highBidder == address(0)

        // An arbitrary non-buyer is rejected by onlyBuyer.
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        a.confirmReceipt(LOT_ID, keccak256("PHOTO"), "ipfs://photo");

        // address(0) equals the zero highBidder so it passes onlyBuyer, but the state guard on an Open
        // lot (deliveryState None) reverts WrongDeliveryState, never silently settling to address(0).
        vm.prank(address(0));
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        a.confirmReceipt(LOT_ID, keccak256("PHOTO"), "ipfs://photo");
    }

    // Cross-clone role isolation. Roles are stored addresses set per-clone in initialize, never a
    // shared / global slot. A role check reading a shared slot would pass every wrong-caller and
    // positive test above yet let clone B's arbiter drive clone A; these pin per-clone keying.

    /// Two sessions with distinct arbiter + pauser configs. Session A's arbiter is admitted on A
    /// (passes onlyArbiter, reaches WrongDeliveryState on its Open lot) but rejected Unauthorized on
    /// B's resolveDispute, and symmetrically. Same for onlyPauser (each clone's pauser toggles its own
    /// state but is Unauthorized on the other). A shared role slot would make the cross-clone calls
    /// pass.
    function test_CrossCloneRoleIsolation() public {
        // Session A: arbiter == `arbiter`, pauser == `pauser` (the named actors).
        SessionAuction a = _sessionWithOpenLot();

        // Session B: distinct arbiter (bidder2), distinct pauser (bidder3), its own Open lot. It needs
        // a distinct sessionId because the factory keys clones by cfg.sessionId (createSession reverts
        // SessionExists on reuse, and cloneDeterministic collides on the same salt), so reusing
        // SESSION_ID would revert before B is created.
        InitConfig memory cfgB = _defaultInitConfig(address(0));
        cfgB.sessionId = keccak256("HAMMER_E2E_SESSION_B"); // distinct id so the factory clones session B
        cfgB.arbiter = bidder2; // != A's arbiter
        cfgB.pauser  = bidder3; // != A's pauser
        SessionAuction b = SessionAuction(hammer.createSession(cfgB));
        vm.prank(address(hammer));
        b.openLot(LOT_ID, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));

        // onlyArbiter isolation.
        // A's arbiter is admitted on A: passes onlyArbiter, reaches the Open-lot state guard.
        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        a.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, keccak256("PHOTO"));

        // A's arbiter is rejected on B (B's stored arbiter is bidder2): Unauthorized, not the state guard.
        vm.prank(arbiter);
        vm.expectRevert(UNAUTHORIZED);
        b.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, keccak256("PHOTO"));

        // Symmetric: B's arbiter (bidder2) is admitted on B but Unauthorized on A.
        vm.prank(bidder2);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        b.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, keccak256("PHOTO"));

        vm.prank(bidder2);
        vm.expectRevert(UNAUTHORIZED);
        a.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, keccak256("PHOTO"));

        // onlyPauser isolation.
        // A's pauser (`pauser`) is Unauthorized on B (B's stored pauser is bidder3).
        vm.prank(pauser);
        vm.expectRevert(UNAUTHORIZED);
        b.pause();

        // B's pauser (bidder3) is Unauthorized on A.
        vm.prank(bidder3);
        vm.expectRevert(UNAUTHORIZED);
        a.pause();

        // Each clone's pauser toggles its own state and that pause does not leak: the paused() reads
        // catch a shared slot (which would flip both), the Paused event from address(a) names this
        // clone's pauser and catches a clone that stamps the wrong account.
        vm.expectEmit(false, false, false, true, address(a));
        emit Pausable.Paused(pauser);
        vm.prank(pauser);
        a.pause();
        assertTrue(a.paused(), "A's pauser pauses A");
        assertFalse(b.paused(), "A's pause must NOT leak to B (per-clone Pausable state)");

        // B's pauser pauses B only; B's Paused event from address(b) names B's distinct pauser
        // (bidder3). Two different accounts on two clones pins per-clone identity.
        vm.expectEmit(false, false, false, true, address(b));
        emit Pausable.Paused(bidder3);
        vm.prank(bidder3);
        b.pause();
        assertTrue(b.paused(), "B's pauser pauses B");
        assertTrue(a.paused(), "B's pause must NOT clear A (per-clone Pausable state)");
    }

    /// Same-clone cross-role confusion: one privileged role must not pass another role's gate on the
    /// same clone (e.g. onlyHammer aliased `|| msg.sender == _settler`, or onlyArbiter reading
    /// _settler), which would let the settler openLot / voidSession or the pauser resolveDispute. The
    /// actors are distinct addresses, so each row pins that a gate keys to its own stored slot and
    /// rejects every other privileged role with Unauthorized.
    function test_SameCloneRoleConfusionMatrix() public {
        SessionAuction a = _sessionWithOpenLot(); // roles wired to the distinct named actors

        // onlyHammer keyed to _hammer only: the settler (privileged, not the hammer) is rejected on
        // openLot, catching a `|| msg.sender == _settler` alias.
        vm.prank(settler);
        vm.expectRevert(UNAUTHORIZED);
        a.openLot(2, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));

        // onlyHammer keyed to _hammer only: the arbiter is rejected on voidSession (the panic button is
        // the factory's alone), catching onlyHammer aliased to _arbiter.
        vm.prank(arbiter);
        vm.expectRevert(UNAUTHORIZED);
        a.voidSession("operator-panic");

        // onlySettler keyed to _settler only: the arbiter is rejected on commitBidBook.
        vm.prank(arbiter);
        vm.expectRevert(UNAUTHORIZED);
        a.commitBidBook(LOT_ID, keccak256("ROOT"));

        // onlySettler keyed to _settler only: the pauser is rejected on commitBidBook.
        vm.prank(pauser);
        vm.expectRevert(UNAUTHORIZED);
        a.commitBidBook(LOT_ID, keccak256("ROOT"));

        // onlyArbiter keyed to _arbiter only: the settler and the pauser are both rejected on
        // resolveDispute. The modifier runs before the state guard, so the revert is Unauthorized, not
        // WrongDeliveryState. Catches onlyArbiter wired to _settler or _pauser.
        vm.prank(settler);
        vm.expectRevert(UNAUTHORIZED);
        a.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, keccak256("PHOTO"));

        vm.prank(pauser);
        vm.expectRevert(UNAUTHORIZED);
        a.resolveDispute(LOT_ID, Resolution.ReleaseToSeller, keccak256("PHOTO"));

        // onlyArbiter keyed to _arbiter only on the integrity resolver too: the settler is rejected on
        // resolveBidIntegrityDispute (the modifier runs before any dispute-state lookup).
        vm.prank(settler);
        vm.expectRevert(UNAUTHORIZED);
        a.resolveBidIntegrityDispute(LOT_ID, 1, true, 0);

        // onlyPauser keyed to _pauser only: the arbiter and the settler are both rejected on pause()
        // (_defaultInitConfig wires a distinct pauser, so neither holds the pause role).
        vm.prank(arbiter);
        vm.expectRevert(UNAUTHORIZED);
        a.pause();

        vm.prank(settler);
        vm.expectRevert(UNAUTHORIZED);
        a.pause();
    }

    /// initialize is gated by the OZ `initializer` modifier (single-shot, reverting
    /// InvalidInitialization), not by a role: any caller may invoke it on a fresh clone, the factory
    /// just does so atomically. This pins that a non-hammer caller's initialize on a fresh clone does
    /// not revert Unauthorized. The single-shot and impl-locked guards are covered in A_Lifecycle.t.sol.
    function test_InitializeNotGatedByHammerRole() public {
        // Fresh uninitialized clone of the locked impl. Clones.clone does not run the impl's
        // constructor, so _disableInitializers was never invoked on this instance. A
        // `new SessionAuction()` would not work: its constructor runs _disableInitializers, so its
        // initialize would revert InvalidInitialization instead of exercising the any-caller path.
        SessionAuction fresh = SessionAuction(Clones.clone(address(impl)));

        // A non-hammer caller (bidder1) initializes the fresh clone; the revert (if any) must not be
        // Unauthorized. The default cfg is valid so the call succeeds, flipping red only if someone
        // bolts onlyHammer onto initialize.
        vm.prank(bidder1); // not address(hammer)
        _assertNotUnauthorized(
            address(fresh),
            abi.encodeCall(ISessionAuction.initialize, (_defaultInitConfig(address(0))))
        );
    }

    // Auxiliary-contract access (Treasury / OperatorBond), three parts.
    //
    // Gated: Treasury (depositForfeit onlyAuction, challenge onlyOffender, resolveChallenge
    // onlyArbiter) and OperatorBond (recordClaim / slashNonLiveness onlyAuction) reject the wrong
    // caller with Unauthorized (test_AuxiliaryAccessGates), and onlyAuction admits a factory-registered
    // clone (test_AuxiliaryOnlyAuctionAdmitsClone).
    //
    // Ungated: Treasury.disburse and OperatorBond.settleSlash carry no caller gate (they succeed
    // permissionlessly after their windows), so an arbitrary caller must reach the body, not an
    // Unauthorized revert (tail of test_AuxiliaryAccessGates).
    //
    // The gatekeeper: onlyAuction is only as strong as the registerClone admission that populates the
    // clone set, so registerClone must itself be gated to the Hammer factory, else a rejected EOA
    // could self-register first. The negative (test_RevertWhen_RegisterCloneSelfRegistration) and
    // positive (test_RegisterCloneAdmitsAuthorizedRegistrar) cover both sides. The SessionAuction-side
    // arbiter gate (resolveBidIntegrityDispute) is asserted in its own test.

    function test_AuxiliaryAccessGates() public {
        // Treasury.depositForfeit is onlyAuction (factory-registered clone set): an arbitrary
        // non-clone caller is rejected with Unauthorized.
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        treasury.depositForfeit(bidder1, bidder2, LOT_ID, 1 ether, 1 ether, 1 ether, seller);

        // Treasury.challenge is onlyOffender: a caller that is not the recorded offender of the
        // forfeit is rejected with Unauthorized.
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        treasury.challenge{value: DISPUTE_BOND_AMT}(keccak256("FORFEIT_ID"));

        // Treasury.resolveChallenge is onlyArbiter: a non-arbiter caller is rejected.
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        treasury.resolveChallenge(keccak256("FORFEIT_ID"), false);

        // OperatorBond.recordClaim is onlyAuction (SessionAuction clone as caller): a non-clone
        // caller is rejected with Unauthorized.
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        operatorBond.recordClaim(SESSION_ID, bidder2, 1);

        // OperatorBond.slashNonLiveness is onlyAuction: a non-clone caller is rejected.
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        operatorBond.slashNonLiveness(SESSION_ID, LOT_ID);

        // Ungated / permissionless half: no caller gate on the payout / slash path.
        // Treasury.disburse and OperatorBond.settleSlash succeed permissionlessly after their windows,
        // so an arbitrary caller must reach the body, never Unauthorized. Flips red only if someone
        // bolts an onlyArbiter / onlyAuction gate onto disburse / settleSlash.
        vm.prank(bidder1);
        _assertNotUnauthorized(
            address(treasury),
            abi.encodeCall(ITreasury.disburse, (keccak256("FORFEIT_ID")))
        );

        vm.prank(bidder1);
        _assertNotUnauthorized(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.settleSlash, (SESSION_ID))
        );
    }

    /// The whole onlyAuction premise collapses if registerClone is ungated: if any EOA can call
    /// registerClone(self) it joins the clone set and thereafter passes every onlyAuction gate. Only
    /// the Hammer factory should register clones, so an EOA must be rejected. First an arbitrary-EOA
    /// registerClone(self) on both auxiliary contracts must revert (not silently succeed), then chained
    /// the same EOA is still rejected Unauthorized on depositForfeit / recordClaim / slashNonLiveness,
    /// proving it never joined the clone set.
    function test_RevertWhen_RegisterCloneSelfRegistration() public {
        // An arbitrary EOA tries to self-register on both auxiliary contracts. registerClone has the
        // same signature across ITreasury / IOperatorBond, so the helper's ITreasury.registerClone
        // encoding is byte-identical for the operatorBond target. Each must revert, never silently
        // admit bidder1 to the clone set.
        vm.prank(bidder1);
        _assertRegisterCloneRejected(address(treasury), bidder1);

        vm.prank(bidder1);
        _assertRegisterCloneRejected(address(operatorBond), bidder1);

        // Chained: since self-registration was rejected, bidder1 is not in the clone set and the
        // onlyAuction gates still reject it Unauthorized. An ungated registerClone that admitted
        // bidder1 above would flip these to a non-Unauthorized body revert.
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        treasury.depositForfeit(bidder1, bidder2, LOT_ID, 1 ether, 1 ether, 1 ether, seller);

        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        operatorBond.recordClaim(SESSION_ID, bidder2, 1);

        // slashNonLiveness is the third onlyAuction gate on the same membership: rejected there too.
        vm.prank(bidder1);
        vm.expectRevert(UNAUTHORIZED);
        operatorBond.slashNonLiveness(SESSION_ID, LOT_ID);
    }

    /// Positive side of the registerClone gate: a registerClone that rejects everyone would satisfy
    /// the self-registration negative yet brick the deploy path. This pins that the legitimate
    /// registrar is not rejected Unauthorized (authority-gated, not reject-all).
    ///
    /// treasury / operatorBond are deployed in HammerBase.setUp() via plain `new Treasury()` /
    /// `new AgentBond()` (no constructor authority arg), so their authority is the deployer
    /// (address(this)), not the Hammer factory. So the deployer (no prank) is not rejected on
    /// registerClone for both; pranking address(hammer) instead would fail.
    function test_RegisterCloneAdmitsAuthorizedRegistrar() public {
        // No prank: msg.sender == address(this), the deployer of treasury / operatorBond. It must pass
        // the gate on both.
        _assertNotUnauthorized(
            address(treasury),
            abi.encodeCall(ITreasury.registerClone, (address(auction)))
        );

        _assertNotUnauthorized(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.registerClone, (address(auction)))
        );
    }

    /// Positive onlyAuction: a factory-registered clone is admitted past onlyAuction on
    /// Treasury.depositForfeit / OperatorBond.recordClaim / OperatorBond.slashNonLiveness, proving the
    /// gate is keyed to clone-set membership, not reject-all. The factory is the only registrar, so
    /// this builds the session via createSession, pranks the clone, and asserts each call is not
    /// Unauthorized. ERC-20 rail so depositForfeit's native msg.value check is not the first failure.
    function test_AuxiliaryOnlyAuctionAdmitsClone() public {
        hammer.setPaymentTokenAllowed(address(token), true);
        SessionAuction a = _newSession(address(token)); // factory registers the clone on Treasury + OperatorBond
        address clone = address(a);

        // depositForfeit: the registered clone passes onlyAuction, then hits a body revert that is not
        // Unauthorized. Pranked as the clone, ERC-20 rail (msg.value == 0 path).
        vm.prank(clone);
        _assertNotUnauthorized(
            address(treasury),
            abi.encodeCall(
                ITreasury.depositForfeit,
                (bidder1, bidder2, LOT_ID, 1 ether, 1 ether, 1 ether, seller)
            )
        );

        // recordClaim: the registered clone must pass onlyAuction.
        vm.prank(clone);
        _assertNotUnauthorized(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.recordClaim, (SESSION_ID, bidder2, 1))
        );

        // slashNonLiveness: the registered clone must pass onlyAuction.
        vm.prank(clone);
        _assertNotUnauthorized(
            address(operatorBond),
            abi.encodeCall(IOperatorBond.slashNonLiveness, (SESSION_ID, LOT_ID))
        );
    }

    // Payment-token allowlist. createSession refuses any ERC-20 not vetted by the house, so a
    // fee-on-transfer / rebasing token can never back a session escrow. Native ETH (address(0)) is
    // always permitted. The factory owner is this test contract (it deployed `hammer` in
    // HammerBase.setUp).

    /// @dev A non-allowlisted ERC-20 paymentToken is rejected at createSession (the sole production
    ///      path).
    function test_CreateSessionRejectsNonAllowlistedToken() public {
        assertFalse(hammer.isPaymentTokenAllowed(address(token)), "token starts non-allowlisted");
        InitConfig memory cfg = _defaultInitConfig(address(token));

        vm.expectRevert(abi.encodeWithSelector(Hammer.PaymentTokenNotAllowed.selector, address(token)));
        hammer.createSession(cfg);
    }

    /// @dev Once the owner allowlists the ERC-20, createSession wires a clone on that rail.
    function test_CreateSessionAcceptsAllowlistedToken() public {
        hammer.setPaymentTokenAllowed(address(token), true);
        assertTrue(hammer.isPaymentTokenAllowed(address(token)), "ERC-20 now allowlisted");

        InitConfig memory cfg = _defaultInitConfig(address(token));
        address clone = hammer.createSession(cfg);
        assertEq(SessionAuction(clone).paymentToken(), address(token), "clone wired to the ERC-20 rail");
    }

    /// @dev Native ETH needs no allowlist entry: isPaymentTokenAllowed(0) is true and createSession passes.
    function test_CreateSessionNativeNeedsNoAllowlist() public {
        assertTrue(hammer.isPaymentTokenAllowed(address(0)), "native ETH is always allowed");
        hammer.createSession(_defaultInitConfig(address(0))); // no revert, no allowlist entry
    }

    /// @dev setPaymentTokenAllowed is owner-gated (the house KYC operator that also gates createSession).
    function test_RevertWhen_SetPaymentTokenAllowedNotOwner() public {
        vm.prank(bidder1);
        vm.expectRevert(abi.encodeWithSelector(Ownable.OwnableUnauthorizedAccount.selector, bidder1));
        hammer.setPaymentTokenAllowed(address(token), true);
    }

    /// @dev Allowlisting address(0) is rejected, so the native-always-allowed flag stays unambiguous.
    function test_RevertWhen_AllowlistNativeSentinel() public {
        vm.expectRevert(abi.encodeWithSelector(Hammer.PaymentTokenNotAllowed.selector, address(0)));
        hammer.setPaymentTokenAllowed(address(0), true);
    }
}
