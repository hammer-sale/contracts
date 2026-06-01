// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Session-void strand-safety: under voidSession every party can recover everything they are owed
// via withdrawRefund, with no funds stranded on the clone.
//
// voidSession is onlyHammer and O(1): it sets the voided flag and emits SessionVoided with no
// per-lot loop; a non-hammer caller reverts Unauthorized.
//
// withdrawRefund pays in three steps, each gated on the void (except the terminal-refundable
// fast path):
//   step 1 (deposit refund): the caller gets exactly free+committed, zeroed before the pay; a
//     repeat or zero-balance pull reverts NothingToWithdraw; a non-voided non-terminal lot
//     reverts SessionIsVoided.
//   step 2 (winner escrow): the highBidder also recovers lot.escrowAmount, drives phase and
//     deliveryState to Refunded, and emits DepositWithdrawn + Refunded, across every non-terminal
//     phase; a losing bidder never reaches the escrow; an escrowAmount==0 terminal lot is a safe
//     no-op.
//   step 3 (dispute bond): lot.disputeOpener reclaims lot.disputeBond in full once, whether
//     opener==winner or opener!=winner; resolveDispute is then unreachable.
//
// End-to-end conservation on a mixed session: sum withdrawn == sum deposited+bonded, on both the
// native and ERC-20 rails.
//
// Adversarial / no-strand cases:
//   - withdrawRefund is nonReentrant: a re-entrant native receiver hits ReentrancyGuardReentrantCall.
//   - hostile payee: a reverting native receiver / a false-returning token parks to pending
//     withdrawals (WithdrawalCredited), then claimPending pulls it (WithdrawalClaimed).
//   - escrow single-exit ordering: whichever of {withdrawRefund step 2, _release} runs first wins;
//     the loser of the race reverts a phase guard.
//   - voidAndAward-then-voidSession: the promoted winner (not the offender) pulls escrowAmount.
//
// Negative assertions use a specific selector (never a bare expectRevert).

import {HammerBase} from "./HammerBase.t.sol";

import {Vm} from "forge-std/Vm.sol";

import {SessionAuction} from "../src/SessionAuction.sol";
import {Clones} from "@openzeppelin/contracts/proxy/Clones.sol";
import {ISessionAuction} from "../src/interfaces/ISessionAuction.sol";
import {IFlagRegistry} from "../src/interfaces/IFlagRegistry.sol";
import {IPaddleRegistry} from "../src/interfaces/IPaddleRegistry.sol";
import {MockERC20} from "./mocks/MockERC20.sol";

import {ReentrancyGuardTransient} from "@openzeppelin/contracts/utils/ReentrancyGuardTransient.sol";
import {IERC1271} from "@openzeppelin/contracts/interfaces/IERC1271.sol";
import {ECDSA} from "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";

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

contract SessionVoidTest is HammerBase {
    // Fixture constants.
    uint256 private constant LOT = 1; // winner / single-lot tests
    uint256 private constant LOT2 = 2; // second lot for the mixed-session conservation test
    uint256 private constant LOT3 = 3; // disputed lot for the mixed-session conservation test

    // Distinct KYC paddles (nonzero == registered).
    uint16 private constant PADDLE_WINNER = 700;
    uint16 private constant PADDLE_LOSER = 600;
    uint16 private constant PADDLE_L2 = 500;
    uint16 private constant PADDLE_W2 = 480; // LOT2 winner (mixed session)
    uint16 private constant PADDLE_OFFENDER = 710; // voidAndAward-then-voidSession case
    uint16 private constant PADDLE_PROMOTED = 690;

    // Native rail amounts. Winner deposits more than they bid, so post-hammer the winner Deposit is
    // {free: slack, committed: 0} and escrowAmount == bid (step 1 returns slack, step 2 returns escrow).
    uint128 private constant WIN_BID = 60 ether; // clearing price == escrow at hammer
    uint256 private constant WIN_DEPOSIT = 100 ether;
    uint128 private constant WIN_SLACK = 40 ether; // WIN_DEPOSIT - WIN_BID

    // Offender bids higher than the promoted winner from a WIN_DEPOSIT deposit, so post-void its free
    // slack == WIN_DEPOSIT - OFFENDER_BID.
    uint128 private constant OFFENDER_BID = 70 ether; // > WIN_BID; slack == 30 ether

    // Loser deposits then is outbid (committed -> free); step 1 returns their whole deposit.
    uint128 private constant LOSE_BID = 10 ether;
    uint256 private constant LOSE_DEPOSIT = 30 ether;

    // ERC-20 rail mirrors (6-decimal token), same ratios scaled to 1e6 base.
    uint128 private constant WIN_BID_T = 60e6;
    uint256 private constant WIN_DEPOSIT_T = 100e6;
    uint128 private constant WIN_SLACK_T = 40e6;
    uint128 private constant LOSE_BID_T = 10e6;
    uint256 private constant LOSE_DEPOSIT_T = 30e6;
    // Token-scaled reserve floor. The native RESERVE_PRICE (1e18) is far above the 6-decimal token bids
    // (10e6/60e6), so an ERC-20 lot opened at RESERVE_PRICE would reject every token bid as BidTooLow;
    // 1e6 is the proportional mirror, below LOSE_BID_T so the opening bid clears the reserve.
    uint96 private constant RESERVE_PRICE_T = 1e6;

    address private winner; // in-flight winner (highBidder); recovers escrow under void
    uint256 private winnerKey;
    address private loser; // outbid bidder; recovers free+committed only
    uint256 private loserKey;
    address private loser2; // genuine loser on LOT2 (deposited, outbid, never highBidder)
    uint256 private loser2Key;
    address private winner2; // LOT2 winner (highBidder, escrow); makes loser2 a true loser bucket
    uint256 private winner2Key;
    address private relayer; // arbitrary submitter (proves permissionless pull)
    uint256 private offenderKey; // seeded in setUp for the deterministic g_offender_for_void address

    // Native-rail sentinel (value address(0)) held in storage rather than passed as a literal. The
    // conservation flow branches on `payToken == address(0)` in many inlined helpers; a literal
    // address(0) lets solc fold the branch and inline the whole native chain into one frame, overflowing
    // the via-ir stack-slot budget. Reading the rail from storage keeps the comparison a runtime branch
    // so both rails share one generic frame. Set in setUp.
    address private nativeRail;

    // principal -> signer-key map for contract bidders (the G_ ERC-1271 adversaries), whose address is
    // only known after `new`. _signerKeyFor falls back to this for any principal not in the named-EOA
    // arms, so the map covers every contract principal these tests bid as.
    mapping(address => uint256) private _boundKey;

    function setUp() public override {
        super.setUp();

        (winner, winnerKey) = makeAddrAndKey("g_winner");
        (loser, loserKey) = makeAddrAndKey("g_loser");
        (loser2, loser2Key) = makeAddrAndKey("g_loser2");
        (winner2, winner2Key) = makeAddrAndKey("g_winner2");
        relayer = makeAddr("g_relayer");
        (, offenderKey) = makeAddrAndKey("g_offender_for_void");

        fundEth(winner, INITIAL_ETH);
        fundEth(loser, INITIAL_ETH);
        fundEth(loser2, INITIAL_ETH);
        fundEth(winner2, INITIAL_ETH);
        fundEth(relayer, INITIAL_ETH);

        fundToken(winner, INITIAL_TOKEN);
        fundToken(loser, INITIAL_TOKEN);
        fundToken(loser2, INITIAL_TOKEN);
        fundToken(winner2, INITIAL_TOKEN);

        nativeRail = address(0); // native sentinel in storage (defeats constant-fold inlining)
    }

    // voidSession: onlyHammer, sets the voided flag and emits SessionVoided in O(1); non-hammer reverts.

    /// The configured hammer voids the session: SessionVoided(SESSION_ID, reason) is emitted and the
    /// voided flag is set. Observable proxy: withdrawRefund on a non-terminal lot no longer reverts
    /// SessionIsVoided (its guard `!voided && !terminalRefundable` passes once voided).
    function test_VoidSessionO1() external {
        _initNative();
        _openLot(LOT);

        string memory reason = "ring-detected: session-wide void";

        vm.expectEmit(true, false, false, true, address(auction));
        emit ISessionAuction.SessionVoided(SESSION_ID, reason);
        vm.prank(address(hammer));
        auction.voidSession(reason);

        // Now voided: a caller with no balance reaches the step-1 amount==0 check (NothingToWithdraw)
        // instead of the pre-void SessionIsVoided guard.
        vm.prank(relayer);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(LOT);
    }

    /// voidSession touches one storage flag and emits, with no loop over lots. Open many lots, then
    /// assert its gas stays well under any per-lot-iteration cost. The cap is a structural
    /// no-iteration guard, not an exact-gas pin.
    function test_VoidSessionDoesNotIterateLots() external {
        _initNative();

        for (uint256 i = 1; i <= 25; i++) {
            _openLot(i);
        }

        vm.prank(address(hammer));
        uint256 gasBefore = gasleft();
        auction.voidSession("bulk-void");
        uint256 gasUsed = gasBefore - gasleft();

        // One cold SSTORE (~20k) plus a string-data event is well under this bound; iterating 25 lots
        // (each a cold SLOAD + branch) would not be.
        assertLt(gasUsed, 100_000, "voidSession appears to iterate lots (gas scales with N)");
    }

    /// A caller that is not the stored hammer reverts Unauthorized.
    function test_RevertWhen_VoidSessionNotHammer() external {
        _initNative();
        _openLot(LOT);

        vm.prank(relayer); // not address(hammer)
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.voidSession("unauthorized-void");
    }

    // withdrawRefund step 1: deposit refund (every caller's free + committed, once, by pull).

    /// An outbid loser holds free+committed (their whole deposit). Under a void, one withdrawRefund
    /// returns exactly free+committed (zeroed before the pay) and emits DepositWithdrawn; a second
    /// call reverts NothingToWithdraw. Native rail.
    function test_WithdrawRefundDeposits() external {
        _initNative();
        _openLot(LOT);

        // loser bids, then winner outbids: loser's committed moves back to free, so loser holds
        // free == LOSE_DEPOSIT, committed == 0.
        _depositNative(loser, LOSE_DEPOSIT);
        _depositNative(winner, WIN_DEPOSIT);
        _placeBidNative(loser, 0, LOSE_BID, PADDLE_LOSER, 0);
        _placeBidNative(winner, 0, WIN_BID, PADDLE_WINNER, LOSE_BID);

        vm.prank(address(hammer));
        auction.voidSession("void");

        uint256 expected = LOSE_DEPOSIT; // free(LOSE_DEPOSIT) + committed(0)
        uint256 balBefore = loser.balance;

        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.DepositWithdrawn(LOT, loser, expected);
        vm.prank(loser);
        auction.withdrawRefund(LOT);

        assertEq(loser.balance - balBefore, expected, "loser delta != free+committed");
        assertEq(auction.withdrawableFree(LOT, loser), 0, "free not zeroed after refund");

        // Second pull: nothing left -> NothingToWithdraw (balance zeroed before the pay).
        vm.prank(loser);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(LOT);
    }

    /// Negative guards: without a void, a non-terminal lot reverts SessionIsVoided; under a void a
    /// zero-balance caller reverts NothingToWithdraw (step-1 amount==0, no escrow/bond).
    function test_RevertWhen_WithdrawRefundNotVoided() external {
        _initNative();
        _openLot(LOT);

        // Give loser a balance so SessionIsVoided (which runs before the step-1 amount==0 check) is
        // unambiguously what reverts on the non-voided non-terminal lot.
        _depositNative(loser, LOSE_DEPOSIT);

        vm.prank(loser);
        vm.expectRevert(ISessionAuction.SessionIsVoided.selector);
        auction.withdrawRefund(LOT);

        // Voided: a caller with no balance reaches step-1 amount==0 -> NothingToWithdraw.
        vm.prank(address(hammer));
        auction.voidSession("void");
        vm.prank(relayer); // never deposited, never bid, not the winner
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(LOT);
    }

    // withdrawRefund step 2: winner escrow no-strand. Run for each non-terminal phase.

    /// highBidder under a void recovers free + escrowAmount in one pull, zeroes escrowAmount, drives
    /// phase + deliveryState to Refunded, emits DepositWithdrawn(free+escrow) AND Refunded(escrow); a
    /// second pull reverts NothingToWithdraw; later releaseAfterWindow / resolveDispute cannot re-pay
    /// the escrow. Phase Hammered (DeliveryState None).
    function test_WithdrawRefundWinnerEscrowNoStrand() external {
        _hammeredWinnerNative(); // LOT Hammered, escrowAmount == WIN_BID, winner free == WIN_SLACK
        _assertWinnerEscrowExit(LOT, winner, WIN_SLACK, WIN_BID);
    }

    /// Phase Voided: the promoted winner of a voidAndAward-ed lot recovers free + escrowAmount
    /// identically. Step 2 is gated on escrowAmount != 0, not a DeliveryState allow-list.
    function test_WithdrawRefundWinnerEscrowNoStrand_Voided() external {
        _votedPromotedWinnerNative(); // LOT Voided; highBidder == winner (promoted), escrow == WIN_BID
        _assertWinnerEscrowExit(LOT, winner, WIN_SLACK, WIN_BID);
    }

    /// Phase Awaiting: an Awaiting winner (DeliveryState.AwaitingDelivery) recovers free +
    /// escrowAmount with no seller-delivery wait and no bond.
    function test_WithdrawRefundWinnerEscrowNoStrand_Awaiting() external {
        _driveToAwaitingNative(); // LOT Awaiting / AwaitingDelivery, escrow == WIN_BID
        _assertWinnerEscrowExit(LOT, winner, WIN_SLACK, WIN_BID);
    }

    /// Phase Delivered: a Delivered winner recovers free + escrowAmount under a void.
    function test_WithdrawRefundWinnerEscrowNoStrand_Delivered() external {
        _driveToDeliveredNative(); // LOT Delivered, escrow == WIN_BID
        _assertWinnerEscrowExit(LOT, winner, WIN_SLACK, WIN_BID);
    }

    /// Phase Disputed: a Disputed winner recovers free + escrowAmount. The winner is not the opener
    /// here (opener == seller), so the bond (step 3) belongs to the seller; the winner's pull returns
    /// exactly free + escrow (no bond). The bond-to-opener path is covered separately below.
    function test_WithdrawRefundWinnerEscrowNoStrand_Disputed() external {
        _driveToDisputedNative(seller); // LOT Disputed, opener == seller, escrow == WIN_BID

        // The seller (opener, not the winner) holds the refundable bond before the winner pull. The
        // winner's step-2 exit must touch only escrowAmount, never the seller's bond.
        Lot memory pre = auction.getLot(LOT);
        assertEq(uint256(pre.disputeBond), uint256(DISPUTE_BOND_AMT), "seller bond precondition");
        assertEq(pre.disputeOpener, seller, "disputeOpener precondition (seller)");

        _assertWinnerEscrowExit(LOT, winner, WIN_SLACK, WIN_BID);

        // The winner-driven Refunded transition must zero only escrowAmount and leave the seller's
        // bond intact and reclaimable. Localized here since the shared helper does not pin bond survival.
        Lot memory post = auction.getLot(LOT);
        assertEq(
            uint256(post.disputeBond),
            uint256(DISPUTE_BOND_AMT),
            "winner escrow pull cleared the seller's bond (strand)"
        );
        assertEq(post.disputeOpener, seller, "winner escrow pull cleared the disputeOpener");
    }

    /// escrowAmount==0 safe no-op: on a terminal lot (escrow already zeroed) step 2 is inert. Drive
    /// to Released (escrow paid to seller), void, then the highBidder's withdrawRefund returns only
    /// their free slack, emits no Refunded, and leaves phase/deliveryState terminal.
    function test_WithdrawRefundWinnerEscrowZeroIsNoOp() external {
        _driveToReleasedNative(); // LOT Settled / Released; escrowAmount == 0; winner free == WIN_SLACK

        Lot memory before = auction.getLot(LOT);
        assertEq(uint256(before.escrowAmount), 0, "precondition escrowAmount != 0");
        uint8 phaseBefore = before.phase;
        uint8 dsBefore = before.deliveryState;

        vm.prank(address(hammer));
        auction.voidSession("void-after-release");

        uint256 balBefore = winner.balance;

        // Only DepositWithdrawn for the slack; no Refunded (escrow term is 0). expectEmit pins exactly
        // this sequence, so a spurious Refunded diverges; the state asserts below catch a re-drive.
        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.DepositWithdrawn(LOT, winner, WIN_SLACK);
        vm.prank(winner);
        auction.withdrawRefund(LOT);

        assertEq(winner.balance - balBefore, WIN_SLACK, "zero-escrow path paid != slack");

        Lot memory afterLot = auction.getLot(LOT);
        assertEq(uint256(afterLot.escrowAmount), 0, "escrow changed by no-op step 2");
        assertEq(afterLot.phase, phaseBefore, "terminal phase re-driven by no-op step 2");
        assertEq(afterLot.deliveryState, dsBefore, "terminal deliveryState re-driven");
    }

    /// Cross-pay boundary: a losing bidder (msg.sender != lot.highBidder) returns only their own
    /// free+committed and can never reach the winner's escrow.
    function test_WithdrawRefundLoserNeverGetsWinnerEscrow() external {
        _initNative();
        _openLot(LOT);

        // loser bids first, winner outbids: loser holds free == LOSE_DEPOSIT (committed 0).
        _depositNative(loser, LOSE_DEPOSIT);
        _depositNative(winner, WIN_DEPOSIT);
        _placeBidNative(loser, 0, LOSE_BID, PADDLE_LOSER, 0);
        _placeBidNative(winner, 0, WIN_BID, PADDLE_WINNER, LOSE_BID);
        _hammer(LOT); // escrowAmount == WIN_BID, highBidder == winner

        vm.prank(address(hammer));
        auction.voidSession("void");

        uint256 escrowBefore = uint256(auction.getLot(LOT).escrowAmount);
        assertEq(escrowBefore, WIN_BID, "precondition winner escrow snapshotted");

        uint256 balBefore = loser.balance;

        // Loser gets only their own free+committed; emits DepositWithdrawn but never Refunded.
        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.DepositWithdrawn(LOT, loser, LOSE_DEPOSIT);
        vm.prank(loser);
        auction.withdrawRefund(LOT);

        assertEq(loser.balance - balBefore, LOSE_DEPOSIT, "loser got more than own deposit");

        // The winner's escrow is untouched by the loser's pull.
        assertEq(
            uint256(auction.getLot(LOT).escrowAmount),
            escrowBefore,
            "loser pull reached the winner escrow (cross-pay)"
        );
    }

    /// voidAndAward-then-voidSession: after a lot void promotes a clean winner, escrow routes to the
    /// promoted winner, never the offender. Under a subsequent session void the promoted winner
    /// (lot.highBidder) pulls escrowAmount; the offender (no longer highBidder) gets only their
    /// residual free slack (their escrow was forfeited to Treasury at voidAndAward).
    function test_WithdrawRefundEscrowGoesToPromotedNotOffender() external {
        _votedPromotedWinnerNative(); // LOT Voided; offender forfeited; promoted winner == `winner`

        // Deterministic offender (same makeAddr as _votedPromotedWinnerNative). It bid OFFENDER_BID
        // from a WIN_DEPOSIT deposit, so post-void its Deposit is {free: WIN_DEPOSIT - OFFENDER_BID,
        // committed: 0} (committed -> escrow at hammer, escrow -> forfeit at voidAndAward).
        address offender = makeAddr("g_offender_for_void");
        uint256 offenderFree = WIN_DEPOSIT - uint256(OFFENDER_BID);

        // The only clone->Treasury move is voidAndAward's forfeit, already done before this session
        // void. The session-void drain must route nothing to Treasury; snapshot both rails and assert
        // unchanged across every pull below.
        uint256 treasuryNativeBefore = address(treasury).balance;
        uint256 treasuryTokenBefore = token.balanceOf(address(treasury));

        vm.prank(address(hammer));
        auction.voidSession("session-void-after-lot-void");

        uint256 escrowBefore = uint256(auction.getLot(LOT).escrowAmount);
        assertEq(escrowBefore, WIN_BID, "promoted-winner escrow precondition");

        // The clone holds the promoted winner's whole deposit (slack + escrow == WIN_DEPOSIT) plus the
        // offender's residual free slack. The forfeited OFFENDER_BID already left for Treasury. Pinning
        // held here makes the post-drain falls-to-0 assertion a true conservation check.
        assertEq(
            address(auction).balance,
            uint256(WIN_DEPOSIT) + offenderFree,
            "clone-held precondition != promoted deposit + offender residual free"
        );

        // Offender pulls first: returns only their own free slack (DepositWithdrawn, no Refunded) and
        // does not touch the promoted winner's escrow. The held side falls by exactly offenderFree.
        uint256 offBalBefore = offender.balance;
        uint256 heldBeforeOffender = address(auction).balance;
        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.DepositWithdrawn(LOT, offender, offenderFree);
        vm.prank(offender);
        auction.withdrawRefund(LOT);

        assertEq(offender.balance - offBalBefore, offenderFree, "offender got more than own free slack");
        assertEq(
            heldBeforeOffender - address(auction).balance,
            offenderFree,
            "clone-held delta != offender free slack on the offender pull (leak/strand)"
        );
        assertEq(
            uint256(auction.getLot(LOT).escrowAmount),
            escrowBefore,
            "offender pull reached the promoted-winner escrow"
        );

        // After the offender slack is out, the clone holds exactly the promoted winner's deposit.
        assertEq(
            address(auction).balance,
            uint256(WIN_DEPOSIT),
            "clone held != promoted deposit after the offender slack pull (residual strand)"
        );

        // The promoted winner (highBidder) is the only party who can pull the escrow.
        _assertWinnerEscrowExit(LOT, winner, WIN_SLACK, WIN_BID);

        // Lot fully drained: offender slack out, promoted deposit out, forfeit already on Treasury.
        assertEq(address(auction).balance, 0, "voided-then-promoted lot not fully drained on the clone");

        // No session-void refund reached Treasury on either rail.
        assertEq(address(treasury).balance, treasuryNativeBefore, "session-void drain leaked native to Treasury");
        assertEq(
            token.balanceOf(address(treasury)), treasuryTokenBefore, "session-void drain leaked token to Treasury"
        );
    }

    /// voidAndAward on a lot already driven to Refunded (by a step-2 pull under a session void) reverts
    /// NotHammered: its `phase == Hammered` guard fronts the flag proof and the forfeit capture. Without
    /// that guard, voidAndAward would re-run the forfeit on the zeroed escrow and re-lock a promoted
    /// deposit into escrowAmount, double-spending across the two void entrypoints. The candidate +
    /// proofs are well-formed, so reverting proves the phase guard fronts them; the no-side-effect
    /// asserts catch a capture-before-phase-check bug even if the surfaced selector were wrong.
    function test_RevertWhen_VoidAndAwardAfterSessionVoidRefunded() external {
        _hammeredWinnerNative(); // LOT Hammered, escrowAmount == WIN_BID, winner (offender/highBidder) free == WIN_SLACK

        vm.prank(address(hammer));
        auction.voidSession("void");

        // The offender (here `winner`, the highBidder) is made whole: the step-2 exit drives the lot to
        // Refunded and zeroes escrowAmount. The lot is now not Hammered, so a fresh voidAndAward must fail.
        _assertWinnerEscrowExit(LOT, winner, WIN_SLACK, WIN_BID);

        Lot memory pre = auction.getLot(LOT);
        assertEq(pre.phase, uint8(LotPhase.Refunded), "precondition lot not Refunded after the offender pull");
        assertEq(uint256(pre.escrowAmount), 0, "precondition escrow not zeroed after the offender pull");
        uint256 treasuryNativeBefore = address(treasury).balance;

        // Well-formed candidate + flag mocks (highBidder `winner` flagged, `loser` the promotion target),
        // none of which is reached: the phase guard reverts NotHammered first.
        _mockFlagsForVoidAndAward(PADDLE_WINNER, PADDLE_PROMOTED);
        bytes32[] memory inclusion = _membershipProof(PADDLE_WINNER);
        NextCleanCandidate memory cand =
            _promotedCandidate(loser, WIN_BID, PADDLE_PROMOTED, uint40(auction.getLot(LOT).winnerSeq));

        vm.expectRevert(ISessionAuction.NotHammered.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, inclusion, cand);

        // No side effect: the lot is untouched (still Refunded, escrow 0, highBidder unchanged) and
        // Treasury received no spurious zero-forfeit.
        Lot memory post = auction.getLot(LOT);
        assertEq(post.phase, uint8(LotPhase.Refunded), "blocked voidAndAward re-drove the Refunded phase");
        assertEq(post.deliveryState, uint8(DeliveryState.Refunded), "blocked voidAndAward re-drove deliveryState");
        assertEq(uint256(post.escrowAmount), 0, "blocked voidAndAward re-locked escrow on a Refunded lot");
        assertEq(post.highBidder, winner, "blocked voidAndAward overwrote highBidder on a Refunded lot");
        assertEq(
            address(treasury).balance,
            treasuryNativeBefore,
            "blocked voidAndAward routed funds to Treasury (capture-before-phase-check)"
        );
    }

    /// voidSession alone does not freeze voidAndAward. voidAndAward is gated only on phase == Hammered
    /// and the anti-collusion window, and never reads the voided flag, so on a still-Hammered lot with
    /// no winner pull yet it still promotes the next-clean candidate. (The block in the previous test
    /// comes from the step-2 pull flipping the phase to Refunded, not from the voided flag.)
    function test_VoidSessionThenVoidAndAwardOnStillHammeredPromotes() external {
        // LOT Hammered: offender top (flagged), `winner` clean below; promotedSeq is the winner's bid seq.
        (address offender, uint64 promotedSeq) = _hammeredFlaggedOffenderNative();

        // Voided, but no winner pull yet, so the lot is still Hammered.
        vm.prank(address(hammer));
        auction.voidSession("session-void-before-any-pull");
        Lot memory pre = auction.getLot(LOT);
        assertEq(pre.phase, uint8(LotPhase.Hammered), "precondition lot not Hammered after a bare voidSession");
        assertEq(uint256(pre.escrowAmount), uint256(OFFENDER_BID), "precondition escrow != offender bid");
        uint256 treasuryBefore = address(treasury).balance;

        // voidAndAward promotes the clean `winner` (LotVoided carries the true offender, not the
        // promoted bidder) and re-locks the promoted WIN_BID into escrowAmount, succeeding even though
        // the session is voided. The candidate carries the promoted winner's own bid seq, not the
        // offender's lot.winnerSeq (which would revert BadCandidate).
        _mockFlagsForVoidAndAward(PADDLE_OFFENDER, PADDLE_PROMOTED);
        bytes32[] memory inclusion = _membershipProof(PADDLE_OFFENDER);
        NextCleanCandidate memory cand = _promotedCandidate(winner, WIN_BID, PADDLE_PROMOTED, uint40(promotedSeq));

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.LotVoided(LOT, offender, winner, WIN_BID);
        vm.prank(relayer); // permissionless
        auction.voidAndAward(LOT, inclusion, cand);

        // Post-state: Voided, promoted `winner` is highBidder, escrow re-locked to the promoted bid, and
        // the offender's OFFENDER_BID forfeit reached Treasury.
        Lot memory post = auction.getLot(LOT);
        assertEq(post.phase, uint8(LotPhase.Voided), "voidAndAward on a voided-session Hammered lot did not promote");
        assertEq(post.highBidder, winner, "promoted highBidder not the clean winner");
        assertEq(uint256(post.escrowAmount), uint256(WIN_BID), "escrow not re-locked to the promoted bid");
        assertEq(
            address(treasury).balance - treasuryBefore,
            uint256(OFFENDER_BID),
            "offender forfeit did not reach Treasury on the voided-session voidAndAward"
        );

        // The winner-escrow exit still works on the now-Voided lot.
        _assertWinnerEscrowExit(LOT, winner, WIN_SLACK, WIN_BID);
    }

    // withdrawRefund step 3: dispute-bond no-strand.

    /// opener == winner: a Disputed lot whose opener is the winner. Step 2 drives the lot to Refunded
    /// (so resolveDispute can never release the bond), and step 3 returns the bond to the opener in
    /// the same pull. One withdrawRefund returns free + escrow + bond; disputeBond is zeroed; a later
    /// resolveDispute reverts WrongDeliveryState and re-pays nothing.
    function test_WithdrawRefundDisputeBondToOpener() external {
        _driveToDisputedNative(winner); // opener == winner; bond == DISPUTE_BOND_AMT; escrow == WIN_BID

        Lot memory pre = auction.getLot(LOT);
        assertEq(uint256(pre.disputeBond), uint256(DISPUTE_BOND_AMT), "bond precondition");
        assertEq(pre.disputeOpener, winner, "opener precondition");

        // The 3-leg pull (slack + escrow + bond) fires only under a session void.
        vm.prank(address(hammer));
        auction.voidSession("g-04-dispute-bond");

        uint256 expected = uint256(WIN_SLACK) + uint256(WIN_BID) + uint256(DISPUTE_BOND_AMT);
        uint256 balBefore = winner.balance;

        // Held snapshot for the only pull moving all three legs at once: the contract balance must fall
        // by exactly the amount paid (the payee delta and post-state zeros alone do not pin the held
        // side). _pullAndMeasure asserts this per-pull elsewhere but not on this standalone three-leg
        // pull, so check the held invariant here.
        uint256 heldBefore = address(auction).balance;

        // DepositWithdrawn carries the full amount; Refunded carries the escrow leg.
        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.DepositWithdrawn(LOT, winner, expected);
        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.Refunded(LOT, winner, uint256(WIN_BID));
        vm.prank(winner);
        auction.withdrawRefund(LOT);

        assertEq(winner.balance - balBefore, expected, "opener==winner delta != slack+escrow+bond");
        // Held side falls by exactly slack+escrow+bond, no more (leak), no less (strand).
        assertEq(
            heldBefore - address(auction).balance,
            expected,
            "clone-held delta != slack+escrow+bond on the three-leg single pull (leak/strand)"
        );

        Lot memory post = auction.getLot(LOT);
        assertEq(uint256(post.disputeBond), 0, "bond not zeroed before payout");
        assertEq(uint256(post.escrowAmount), 0, "escrow not zeroed");
        assertEq(post.phase, uint8(LotPhase.Refunded), "phase not Refunded");
        assertEq(post.deliveryState, uint8(DeliveryState.Refunded), "deliveryState not Refunded");

        // resolveDispute is now unreachable (lot Refunded, not Disputed). It checks deliveryState ==
        // Disputed first and surfaces WrongDeliveryState before reaching the internal escrowAmount==0
        // -> NoEscrow guard, so the deliveryState guard is what surfaces here.
        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.resolveDispute(LOT, Resolution.RefundToBuyer, keccak256("photo"));
    }

    /// opener != winner: a Disputed lot whose opener is the seller. Under a void the seller (opener)
    /// reclaims the bond in full via step 3 (deposit/escrow legs are 0 for the seller), and the winner
    /// separately pulls the escrow (step 2). Bond and escrow move independently to their rightful
    /// parties, no double-pay.
    ///
    /// The seller's bond-only pull is localized: after it, the winner's escrow slot is still exactly
    /// WIN_BID and the lot is still Awaiting / Disputed (a step-3 that clobbered escrowAmount or
    /// re-drove the phase is caught here, not only at the later winner pull). The pull is wrapped in
    /// vm.recordLogs to assert exactly one DepositWithdrawn and zero Refunded (the seller is not
    /// highBidder, so no Refunded(LOT, seller, 0) may spuriously emit).
    function test_WithdrawRefundDisputeBondToOpenerNotWinner() external {
        _driveToDisputedNative(seller); // opener == seller; bond == DISPUTE_BOND_AMT; escrow == WIN_BID

        // Cross-mutation anchors: the seller's bond-only path must touch neither escrow nor lot state.
        Lot memory preSeller = auction.getLot(LOT);
        assertEq(uint256(preSeller.escrowAmount), uint256(WIN_BID), "winner escrow precondition (opener!=winner)");
        assertEq(preSeller.phase, uint8(LotPhase.Awaiting), "phase precondition Awaiting (opener!=winner)");
        assertEq(preSeller.deliveryState, uint8(DeliveryState.Disputed), "deliveryState precondition Disputed");

        // The opener (seller) reclaims the bond via step 3, which is gated on a session void.
        vm.prank(address(hammer));
        auction.voidSession("g-04-dispute-bond-opener-not-winner");

        // The seller never deposited and is not highBidder, so steps 1 and 2 contribute 0: the pull
        // returns exactly the bond. recordLogs lets us assert exactly-one-DepositWithdrawn-and-zero-Refunded.
        uint256 sellerBefore = seller.balance;
        vm.recordLogs();
        vm.prank(seller);
        auction.withdrawRefund(LOT);

        (uint256 depositWithdrawnCount, uint256 refundedCount) = _countWithdrawEvents(vm.getRecordedLogs(), LOT, seller);
        assertEq(depositWithdrawnCount, 1, "seller bond pull emitted != 1 DepositWithdrawn");
        assertEq(refundedCount, 0, "seller bond pull emitted a spurious Refunded (escrow leg is 0)");

        assertEq(
            seller.balance - sellerBefore, uint256(DISPUTE_BOND_AMT), "opener!=winner bond not returned in full"
        );
        assertEq(uint256(auction.getLot(LOT).disputeBond), 0, "bond not zeroed (opener!=winner)");

        // Cross-mutation localized at the seller pull: winner escrow untouched, lot still Awaiting / Disputed.
        Lot memory postSeller = auction.getLot(LOT);
        assertEq(uint256(postSeller.escrowAmount), uint256(WIN_BID), "seller bond pull touched winner escrow");
        assertEq(postSeller.phase, uint8(LotPhase.Awaiting), "seller bond pull re-drove phase");
        assertEq(
            postSeller.deliveryState, uint8(DeliveryState.Disputed), "seller bond pull re-drove deliveryState"
        );

        // A second seller pull is empty (bond taken, no deposit/escrow) -> NothingToWithdraw.
        vm.prank(seller);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(LOT);

        // The winner independently recovers free + escrow via step 2 (no bond, that was the seller's).
        _assertWinnerEscrowExit(LOT, winner, WIN_SLACK, WIN_BID);
    }

    /// The `+ committed` summand of step 1 (the only test that pins it): a void can fire mid-auction,
    /// leaving the live top bidder on an Open lot with committed == their bid and free == slack. The
    /// step-1 refund (free + committed) zeroes both. There is no committed getter (withdrawableFree
    /// reads only free), so committed is observable only through the refund delta. Deposit WIN_DEPOSIT,
    /// bid WIN_BID, no hammer: the pull must return exactly WIN_DEPOSIT, emit
    /// DepositWithdrawn(WIN_DEPOSIT) and no Refunded (escrow leg is 0; committed must not be misrouted
    /// as an escrow refund). Native.
    function test_WithdrawRefundOpenLotTopBidderCommitted() external {
        _initNative();
        _openLot(LOT);

        // `winner` is the live top bidder on an Open lot: deposit with slack, place the top bid, no
        // hammer. Deposit == {free: WIN_SLACK, committed: WIN_BID}.
        _depositNative(winner, WIN_DEPOSIT);
        _placeBidFor(winner, 0, WIN_BID, PADDLE_WINNER, 0);

        // The lot is still Open (escrowAmount == 0, step 2 cannot contribute) and visible free is only
        // the slack, strictly less than what the pull must return: a free-only refund would strand WIN_BID.
        Lot memory pre = auction.getLot(LOT);
        assertEq(pre.phase, uint8(LotPhase.Open), "precondition lot not Open (was it hammered?)");
        assertEq(uint256(pre.escrowAmount), 0, "precondition escrowAmount != 0 on an un-hammered lot");
        assertEq(auction.withdrawableFree(LOT, winner), uint256(WIN_SLACK), "precondition free != slack");
        assertEq(winner, auction.getLot(LOT).highBidder, "precondition winner is not the live top bidder");

        vm.prank(address(hammer));
        auction.voidSession("mid-auction-panic-void");

        uint256 balBefore = winner.balance;
        // recordLogs: the absence of Refunded is load-bearing (committed is a step-1 deposit refund, not
        // an escrow refund) and vm.expectEmit cannot assert non-emission.
        vm.recordLogs();
        vm.prank(winner);
        auction.withdrawRefund(LOT);
        Vm.Log[] memory pullLogs = vm.getRecordedLogs();

        (uint256 depositWithdrawnCount, uint256 refundedCount) = _countWithdrawEvents(pullLogs, LOT, winner);
        assertEq(depositWithdrawnCount, 1, "open-lot top bidder pull emitted != 1 DepositWithdrawn");
        assertEq(refundedCount, 0, "open-lot top bidder pull emitted a spurious Refunded (no escrow exists)");

        // The DepositWithdrawn amount carries the full free + committed.
        (uint256 emittedLot, address emittedPrincipal, uint256 emittedAmount) =
            _firstDepositWithdrawn(pullLogs, LOT, winner);
        assertEq(emittedLot, LOT, "DepositWithdrawn lotId mismatch");
        assertEq(emittedPrincipal, winner, "DepositWithdrawn principal mismatch");
        assertEq(emittedAmount, uint256(WIN_DEPOSIT), "DepositWithdrawn amount != free + committed");

        assertEq(
            winner.balance - balBefore, uint256(WIN_DEPOSIT), "delta != free + committed (committed stranded?)"
        );
        assertEq(auction.withdrawableFree(LOT, winner), 0, "free not zeroed after refund");
        // Never hammered, so the escrow slot stays 0.
        assertEq(uint256(auction.getLot(LOT).escrowAmount), 0, "escrow slot changed on an un-hammered lot");

        // Second pull: both free and committed zeroed -> NothingToWithdraw.
        vm.prank(winner);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(LOT);
    }

    /// Reverse ordering, opener == seller: step 3 has no phase guard, only `voided && msg.sender ==
    /// lot.disputeOpener && lot.disputeBond != 0`, so the opener reclaims the bond even after step 2
    /// drives the lot to Refunded. Here the winner pulls escrow first (lot -> Refunded, the ordering
    /// that makes resolveDispute unreachable), then the seller reclaims the bond. Catches a step 3
    /// wrongly gated on phase == Disputed, or a step 2 that cleared disputeBond / disputeOpener during
    /// the Refunded transition.
    function test_WithdrawRefundDisputeBondToOpenerAfterWinnerRefunded() external {
        _driveToDisputedNative(seller); // opener == seller; bond == DISPUTE_BOND_AMT; escrow == WIN_BID

        vm.prank(address(hammer));
        auction.voidSession("void-disputed-opener-seller");

        // (1) Winner pulls escrow first: step 2 drives the lot to Refunded and zeroes escrowAmount.
        _assertWinnerEscrowExit(LOT, winner, WIN_SLACK, WIN_BID);

        // (2) The seller's bond must survive the Refunded transition: step 2 zeroes only escrowAmount.
        Lot memory mid = auction.getLot(LOT);
        assertEq(mid.phase, uint8(LotPhase.Refunded), "lot not Refunded after winner escrow pull");
        assertEq(mid.deliveryState, uint8(DeliveryState.Refunded), "deliveryState not Refunded after winner pull");
        assertEq(
            uint256(mid.disputeBond),
            uint256(DISPUTE_BOND_AMT),
            "winner Refunded transition cleared the seller's bond (strand)"
        );
        assertEq(mid.disputeOpener, seller, "winner Refunded transition cleared the disputeOpener");

        // (3) The seller (opener) reclaims exactly the bond via step 3 on the already-Refunded lot (no
        //     phase guard). Not highBidder and never deposited, so steps 1 and 2 contribute 0. recordLogs
        //     asserts exactly-one-DepositWithdrawn and zero Refunded.
        uint256 sellerBefore = seller.balance;
        vm.recordLogs();
        vm.prank(seller);
        auction.withdrawRefund(LOT);
        Vm.Log[] memory bondLogs = vm.getRecordedLogs();

        (uint256 depositWithdrawnCount, uint256 refundedCount) = _countWithdrawEvents(bondLogs, LOT, seller);
        assertEq(depositWithdrawnCount, 1, "seller post-Refunded bond pull emitted != 1 DepositWithdrawn");
        assertEq(refundedCount, 0, "seller post-Refunded bond pull emitted a spurious Refunded");

        (,, uint256 emittedAmount) = _firstDepositWithdrawn(bondLogs, LOT, seller);
        assertEq(emittedAmount, uint256(DISPUTE_BOND_AMT), "seller bond DepositWithdrawn amount != bond");

        assertEq(
            seller.balance - sellerBefore,
            uint256(DISPUTE_BOND_AMT),
            "opener bond not reclaimed in full after the lot was driven to Refunded"
        );

        // Post-state: bond zeroed (paid once), escrow still 0 (winner took it), terminal not re-driven.
        Lot memory post = auction.getLot(LOT);
        assertEq(uint256(post.disputeBond), 0, "bond not zeroed after the opener's post-Refunded reclaim");
        assertEq(uint256(post.escrowAmount), 0, "seller bond pull disturbed the (already 0) escrow");
        assertEq(post.phase, uint8(LotPhase.Refunded), "seller bond pull re-drove the Refunded terminal");
        assertEq(post.deliveryState, uint8(DeliveryState.Refunded), "seller bond pull re-drove deliveryState");

        // A second seller pull is empty (bond gone) -> NothingToWithdraw.
        vm.prank(seller);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(LOT);
    }

    /// The positive terminal-refundable arm: the guard is `if (!voided && !terminalRefundable(phase))
    /// revert SessionIsVoided()`, so a Refunded terminal is served through withdrawRefund as an honest
    /// no-strand exit even without a void. So withdrawRefund must succeed on a terminal-refundable lot
    /// without a void, and still revert SessionIsVoided on a non-refundable terminal (Settled) without
    /// a void. LOT is driven to Refunded via reclaimUndelivered (a losing bidder holds residual free);
    /// LOT2 is driven to Settled via the happy path. No voidSession.
    function test_WithdrawRefundTerminalRefundableNoVoid() external {
        _initNative();
        _openLot(LOT);
        _openLot(LOT2);

        // Place all deposits + bids on both lots before any warp (LOT's reclaim needs a
        // +SELLER_DELIVER_SEC warp that would push past LOT2's endsAt if bidding came after it). LOT:
        // loser bids first, winner outbids, so loser holds free == LOSE_DEPOSIT and is never highBidder.
        // LOT2: winner bids alone (slack WIN_SLACK stays free).
        _depositNative(loser, LOSE_DEPOSIT);
        _depositNative(winner, WIN_DEPOSIT);
        _placeBidFor(loser, 0, LOSE_BID, PADDLE_LOSER, 0);
        _placeBidFor(winner, 0, WIN_BID, PADDLE_WINNER, LOSE_BID);

        _depositNativeLot(winner, LOT2, WIN_DEPOSIT); // independent per-lot nonceKey from LOT
        _placeBidForLot(winner, LOT2, 0, WIN_BID, PADDLE_WINNER, 0);

        // Close + hammer both lots in the same block, then reveal + finalize.
        vm.warp(block.timestamp + 2 days); // past both endsAt
        auction.hammer(LOT);
        auction.hammer(LOT2);
        // Read winnerSeq into locals before vm.prank: an inline auction.getLot(...) staticcall would
        // consume the prank, so reveal would run as the test contract and revert NotPrincipal.
        uint64 wseq1 = auction.getLot(LOT).winnerSeq;
        uint64 wseq2 = auction.getLot(LOT2).winnerSeq;
        vm.prank(winner);
        auction.reveal(LOT, wseq1, WIN_BID, bytes32("salt"));
        vm.prank(winner);
        auction.reveal(LOT2, wseq2, WIN_BID, bytes32("salt"));
        Lot memory hammered = auction.getLot(LOT);
        vm.warp(uint256(hammered.hammeredAt) + AC_CHALLENGE_SEC + 1);
        auction.finalizeWinner(LOT);
        auction.finalizeWinner(LOT2);

        // LOT2 -> Settled via the happy path first (markDelivered + confirmReceipt), before LOT's big warp.
        vm.prank(seller);
        auction.markDelivered(LOT2, keccak256("proof2"), "ipfs://proof2");
        vm.prank(winner);
        auction.confirmReceipt(LOT2, keccak256("photo2"), "ipfs://photo2"); // -> Settled

        // LOT -> Refunded via reclaimUndelivered (seller never delivers): the big warp comes last.
        Lot memory awaiting = auction.getLot(LOT);
        vm.warp(uint256(awaiting.awaitingAt) + SELLER_DELIVER_SEC + 1);
        vm.prank(winner); // the buyer reclaims the undelivered lot
        auction.reclaimUndelivered(LOT);

        // Precondition: LOT is now a terminal-refundable lot, no session void.
        Lot memory refunded = auction.getLot(LOT);
        assertEq(refunded.phase, uint8(LotPhase.Refunded), "LOT not Refunded via reclaimUndelivered");
        assertEq(uint256(refunded.escrowAmount), 0, "reclaimUndelivered did not zero escrow");
        assertEq(auction.withdrawableFree(LOT, loser), uint256(LOSE_DEPOSIT), "loser residual free precondition");

        // Positive arm: the losing bidder's withdrawRefund succeeds without a void (a Refunded lot is
        // terminal-refundable), returning exactly free + committed. recordLogs: no Refunded fires
        // (loser is not highBidder; step-1-only deposit refund).
        uint256 loserBefore = loser.balance;
        vm.recordLogs();
        vm.prank(loser);
        auction.withdrawRefund(LOT); // must NOT revert SessionIsVoided

        (uint256 dwCount, uint256 rCount) = _countWithdrawEvents(vm.getRecordedLogs(), LOT, loser);
        assertEq(dwCount, 1, "terminal-refundable loser pull emitted != 1 DepositWithdrawn");
        assertEq(rCount, 0, "terminal-refundable loser pull emitted a spurious Refunded");
        assertEq(loser.balance - loserBefore, uint256(LOSE_DEPOSIT), "terminal-refundable loser delta != deposit");
        assertEq(auction.withdrawableFree(LOT, loser), 0, "loser free not zeroed on terminal-refundable pull");

        // A second loser pull is empty -> NothingToWithdraw (guard still passes, step-1 amount now 0).
        vm.prank(loser);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(LOT);

        // Precondition: LOT2 is Settled (non-refundable terminal), the winner still holds slack.
        Lot memory settled = auction.getLot(LOT2);
        assertEq(settled.phase, uint8(LotPhase.Settled), "LOT2 not Settled via the happy path");
        assertEq(
            auction.withdrawableFree(LOT2, winner), uint256(WIN_SLACK), "LOT2 winner residual slack precondition"
        );

        // Negative arm: a non-refundable terminal without a void still reverts SessionIsVoided. The
        // winner has a real residual (WIN_SLACK), so the guard (before the step-1 amount==0 check) reverts.
        vm.prank(winner);
        vm.expectRevert(ISessionAuction.SessionIsVoided.selector);
        auction.withdrawRefund(LOT2);
    }

    // End-to-end conservation, both rails. A mixed session covering every bucket exit:
    //   LOT  : winner (escrow) beats loser (free+committed) -> step 2 + step 1.
    //   LOT2 : winner2 (escrow) beats loser2 (free+committed) -> a genuine loser-only bucket
    //          (loser2 deposited + outbid, never highBidder, never escrow; its pull is step-1 only,
    //          emitting only DepositWithdrawn, never Refunded).
    //   LOT3 : winner (escrow) wins then opens a dispute (escrow + bond) -> step 2 + step 3.
    // voidSession; everyone pulls; total out == total in; the clone holds 0 afterward; the five-bucket
    // fund-conservation identity holds before the void and after every pull; per-pull the clone-held
    // balance falls by exactly the amount paid; and zero funds route to Treasury.

    function test_SessionVoidTotalOutEqualsIn() external {
        _sessionVoidConservation(nativeRail); // nativeRail == address(0); storage read, not a literal
    }

    function test_SessionVoidTotalOutEqualsIn_ERC20() external {
        _sessionVoidConservation(address(token));
    }

    /// @dev Rail-parameterized five-bucket conservation across a full session-void drain. Builds a
    ///      mixed session on a fresh clone, records total funded-in (deposits + bond), fires
    ///      voidSession, has every principal pull via withdrawRefund, and asserts:
    ///        (a) each party's balance delta matches their owed amount and the clone-held balance falls
    ///            by exactly that delta on the same pull; a bug that overpays one party and underpays
    ///            another by the same total nets to 0 overall but fails here;
    ///        (b) the sum of all deltas == total in;
    ///        (c) the five-bucket identity (SUM free+committed + SUM escrow + SUM bond + SUM pending ==
    ///            held) holds before voidSession and after every pull;
    ///        (d) the clone's held balance returns to 0 (nothing strands; no pending withdrawals since
    ///            every payee is a plain EOA that accepts the push);
    ///        (e) zero funds route to Treasury across the drain (forfeit-pool isolation).
    function _sessionVoidConservation(address payToken) private {
        SessionAuction a = _mixedSession(payToken);

        // Amounts owed per party (rail-scaled). A winner's owed total on a lot == free slack + escrow
        // == its whole deposit, so the math below uses winDeposit directly.
        uint256 winDeposit = payToken == address(0) ? WIN_DEPOSIT : WIN_DEPOSIT_T;
        uint256 loseDeposit = payToken == address(0) ? LOSE_DEPOSIT : LOSE_DEPOSIT_T;
        uint256 winSlack = payToken == address(0) ? WIN_SLACK : WIN_SLACK_T;
        uint256 winBid = payToken == address(0) ? WIN_BID : WIN_BID_T;
        uint256 bond = uint256(DISPUTE_BOND_AMT);

        // total funded-in held by the clone:
        // LOT:  winner WIN_DEPOSIT + loser LOSE_DEPOSIT
        // LOT2: winner2 WIN_DEPOSIT + loser2 LOSE_DEPOSIT (loser2 is the genuine loser bucket)
        // LOT3: winner WIN_DEPOSIT + bond
        uint256 totalIn = winDeposit + loseDeposit + winDeposit + loseDeposit + winDeposit + bond;
        assertEq(_held(a, payToken), totalIn, "precondition clone holds total funded-in");

        // (c) precondition: the five-bucket identity holds at rest. committed is 0 for all
        // post-hammer/finalize, so the free term == SUM withdrawableFree; asserting it equals `held`
        // pins the per-bucket split, not just the grand total.
        _assertFiveBucket(a, payToken, totalIn, "five-bucket identity violated at rest (pre-void)");

        // Snapshot Treasury on both rails: this session never ran voidAndAward, so Treasury starts at
        // 0 and the session-void drain must leave it at 0.
        uint256 treasuryNativeBefore = address(treasury).balance;
        uint256 treasuryTokenBefore = token.balanceOf(address(treasury));

        vm.prank(address(hammer));
        a.voidSession("mixed-session-void");

        // Every principal pulls; each pull asserts (a) party delta == clone-held delta.
        uint256 sumOut;

        // LOT winner: free + escrow == winDeposit; emits Refunded (step 2).
        sumOut += _pullAndMeasure(a, payToken, winner, LOT, winDeposit, true);
        _assertFiveBucket(a, payToken, totalIn - sumOut, "five-bucket broke after winner LOT pull");

        // LOT loser: free+committed == whole deposit (step 1 only); no Refunded.
        sumOut += _pullAndMeasure(a, payToken, loser, LOT, loseDeposit, false);
        _assertFiveBucket(a, payToken, totalIn - sumOut, "five-bucket broke after loser LOT pull");

        // LOT2 winner2: free + escrow == winDeposit; emits Refunded (step 2).
        sumOut += _pullAndMeasure(a, payToken, winner2, LOT2, winDeposit, true);
        _assertFiveBucket(a, payToken, totalIn - sumOut, "five-bucket broke after winner2 LOT2 pull");

        // LOT2 loser2: the genuine loser-only bucket (step 1 only, no Refunded; not LOT2's highBidder).
        // _pullAndMeasure asserts DepositWithdrawn without a Refunded; the assert below confirms LOT2's
        // escrow is untouched by loser2's pull.
        uint256 lot2EscrowBeforeLoser = uint256(a.getLot(LOT2).escrowAmount); // 0 (winner2 already pulled), but pin it
        sumOut += _pullAndMeasure(a, payToken, loser2, LOT2, loseDeposit, false);
        assertEq(
            uint256(a.getLot(LOT2).escrowAmount),
            lot2EscrowBeforeLoser,
            "loser2 (non-highBidder) pull touched LOT2 escrow (cross-pay)"
        );
        _assertFiveBucket(a, payToken, totalIn - sumOut, "five-bucket broke after loser2 LOT2 pull");

        // LOT3 winner (the Disputed lot's winner and opener): free + escrow + bond.
        sumOut += _pullAndMeasure(a, payToken, winner, LOT3, winDeposit + bond, true);
        _assertFiveBucket(a, payToken, totalIn - sumOut, "five-bucket broke after winner LOT3 pull");

        // (a)/(b) grand total: two pure winners (winDeposit), one disputing winner (winDeposit+bond),
        // two pure losers (loseDeposit each).
        uint256 expectedOut = winDeposit + loseDeposit + winDeposit + loseDeposit + (winDeposit + bond);
        assertEq(winSlack + winBid, winDeposit, "rail slack+bid != deposit (fixture sanity)");
        assertEq(expectedOut, totalIn, "bookkeeping owed != funded-in");
        assertEq(sumOut, totalIn, "sum withdrawn != total deposited+bonded");

        // (d) the clone is fully drained, nothing parked (all payees are plain EOAs).
        assertEq(_held(a, payToken), 0, "clone not fully drained after session-void pulls");
        // (c) final: held == 0 and every bucket zeroed, so the identity holds at 0.
        _assertFiveBucket(a, payToken, 0, "five-bucket identity violated after full drain");

        // (e) no funds routed to Treasury across the entire drain, both rails.
        assertEq(address(treasury).balance, treasuryNativeBefore, "session-void drain leaked native to Treasury");
        assertEq(
            token.balanceOf(address(treasury)), treasuryTokenBefore, "session-void drain leaked token to Treasury"
        );
    }

    // Adversarial / no-strand cases.

    /// withdrawRefund is nonReentrant. A native receiver re-enters withdrawRefund on the _pay push; the
    /// inner call hits the OZ ReentrancyGuardTransient guard and reverts ReentrancyGuardReentrantCall.
    /// The native _pay is gas-capped with a pull-credit fallback (call{gas: 50_000} else credit
    /// _pendingWithdrawals), so the outer call does not bubble the inner revert; it observes a failed
    /// push and parks the amount. Asserts (a) the guard fired with the exact selector (captured by the
    /// attacker's low-level re-entry) and (b) no double-pay: escrow + free zeroed once, paid once.
    /// ISessionAuction declares withdrawRefund external (the modifier is an impl detail), so only a test
    /// catches a missing guard.
    function test_WithdrawRefundReentryIsBlocked() external {
        _initNative();
        _openLot(LOT);

        // Deploy the attacker and land it as the winner so its withdrawRefund hits step 2 (the _pay
        // push to msg.sender). The attacker is an ERC-1271 contract; its bid authorizes via
        // isValidSignature recovering to `winner`, so bind winnerKey for the envelope signature.
        G_ReentrantRefund attacker = new G_ReentrantRefund(auction, LOT, winner);
        _bindKey(address(attacker), winnerKey);
        vm.deal(address(attacker), WIN_DEPOSIT + 1 ether);
        _mockPaddle(address(attacker), PADDLE_WINNER);

        vm.prank(address(attacker));
        auction.depositCeiling{value: WIN_DEPOSIT}(LOT, WIN_DEPOSIT);
        _placeBidFor(address(attacker), 0, WIN_BID, PADDLE_WINNER, 0);
        _hammer(LOT);

        vm.prank(address(hammer));
        auction.voidSession("void");

        uint256 owed = uint256(WIN_SLACK) + uint256(WIN_BID);

        // The outer _pay -> attacker.receive() re-enters withdrawRefund via a low-level call. The guard
        // makes that inner call revert; the attacker swallows + records it and returns normally, so the
        // gas-capped outer push succeeds and the refund is paid directly exactly once.
        uint256 attackerBefore = address(attacker).balance;
        attacker.arm();
        vm.prank(address(attacker));
        auction.withdrawRefund(LOT);

        // (a) The inner call happened and reverted with the OZ guard selector. Readable only because the
        // attacker returns (does not revert) after capturing it: a reverted receive() frame would roll
        // its storage back.
        assertTrue(attacker.reentered(), "G: re-entry was not even attempted");
        assertEq(
            attacker.innerSelector(),
            ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector,
            "G: inner re-entry did not revert ReentrancyGuardReentrantCall"
        );

        // (b) No double-pay: escrow + deposit zeroed once, the full owed amount paid once, nothing parked.
        assertEq(uint256(auction.getLot(LOT).escrowAmount), 0, "G: escrow not zeroed under blocked re-entry");
        assertEq(auction.withdrawableFree(LOT, address(attacker)), 0, "G: free not zeroed under blocked re-entry");
        assertEq(address(attacker).balance - attackerBefore, owed, "G: attacker not paid exactly owed once");
        assertEq(auction.pendingWithdrawal(address(attacker)), 0, "G: nothing should be parked (push accepted)");

        // (c) Single-exit: a second withdrawRefund is empty (deposit + escrow already zeroed).
        vm.prank(address(attacker));
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(LOT);
    }

    /// Hostile-payee no-strand on the withdrawRefund pull. A reverting native receiver as the winner:
    /// withdrawRefund does not revert; it zeroes free + escrow, credits _pendingWithdrawals
    /// (WithdrawalCredited), then claimPending pulls it (WithdrawalClaimed). Native rail.
    function test_WithdrawRefundHostilePayeeNoStrandNative() external {
        _initNative();
        _openLot(LOT);

        // ERC-1271 receiver; its bid authorizes via isValidSignature recovering to `winner`, so bind
        // winnerKey for the envelope signature.
        G_RejectingReceiver hostile = new G_RejectingReceiver(winner);
        _bindKey(address(hostile), winnerKey);
        vm.deal(address(hostile), WIN_DEPOSIT + 1 ether);
        _mockPaddle(address(hostile), PADDLE_WINNER);

        vm.prank(address(hostile));
        auction.depositCeiling{value: WIN_DEPOSIT}(LOT, WIN_DEPOSIT);
        _placeBidFor(address(hostile), 0, WIN_BID, PADDLE_WINNER, 0);
        _hammer(LOT);

        vm.prank(address(hammer));
        auction.voidSession("void");

        uint256 owed = uint256(WIN_SLACK) + uint256(WIN_BID);

        // withdrawRefund does not revert: the failed push is parked and WithdrawalCredited fires.
        vm.expectEmit(true, false, false, true, address(auction));
        emit ISessionAuction.WithdrawalCredited(address(hostile), owed);
        vm.prank(address(hostile));
        auction.withdrawRefund(LOT);

        // Deposit + escrow zeroed (no strand on the lot), the amount parked instead.
        assertEq(auction.withdrawableFree(LOT, address(hostile)), 0, "G: free not zeroed on parked refund");
        assertEq(uint256(auction.getLot(LOT).escrowAmount), 0, "G: escrow not zeroed on parked refund");
        assertEq(auction.pendingWithdrawal(address(hostile)), owed, "G: amount not parked to _pendingWithdrawals");

        // Once the receiver accepts, claimPending pulls the parked amount; WithdrawalClaimed fires.
        hostile.setReject(false);
        uint256 balBefore = address(hostile).balance;
        vm.expectEmit(true, false, false, true, address(auction));
        emit ISessionAuction.WithdrawalClaimed(address(hostile), owed);
        vm.prank(address(hostile));
        auction.claimPending();
        assertEq(address(hostile).balance - balBefore, owed, "G: claimPending did not pay the parked refund");
        assertEq(auction.pendingWithdrawal(address(hostile)), 0, "G: pending not cleared after claim");
    }

    /// Hostile-payee no-strand on the withdrawRefund pull, ERC-20 rail. A token whose transfer
    /// returns false (never reverts) is the payment token; the winner is a plain EOA. trySafeTransfer
    /// observes false and parks to _pendingWithdrawals (no terminal revert); claimPending later
    /// pulls it once the token is toggled to succeed. WithdrawalCredited then WithdrawalClaimed.
    function test_WithdrawRefundHostilePayeeNoStrandERC20() external {
        G_FalseReturningERC20 ftoken = new G_FalseReturningERC20();
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        vm.prank(address(hammer));
        a.initialize(_defaultInitConfig(address(ftoken)));
        vm.prank(address(hammer));
        a.registerOperatorKey(keccak256("OPERATOR_QX_FIXTURE"), keccak256("OPERATOR_QY_FIXTURE"));
        vm.prank(address(hammer));
        // Token-scaled reserve (RESERVE_PRICE_T == 1e6): the bid is WIN_BID_T == 60e6, far below the
        // native RESERVE_PRICE (1e18), so opening at the native reserve would reject it as BidTooLow.
        a.openLot(LOT, seller, RESERVE_PRICE_T, uint64(block.timestamp + 1 days));

        // winner funds + deposits with slack; transferFrom always succeeds so the deposit lands.
        ftoken.mint(winner, WIN_DEPOSIT_T);
        vm.prank(winner);
        ftoken.approve(address(a), WIN_DEPOSIT_T);
        vm.prank(winner);
        a.depositCeiling(LOT, WIN_DEPOSIT_T);

        _mockPaddle(winner, PADDLE_WINNER);
        _placeBidOn(a, winner, 0, WIN_BID_T, PADDLE_WINNER, 0);
        vm.warp(block.timestamp + 2 days);
        a.hammer(LOT);

        vm.prank(address(hammer));
        a.voidSession("void");

        uint256 owed = uint256(WIN_SLACK_T) + uint256(WIN_BID_T);

        // The push leg (token.transfer) returns false: parked, not reverted. WithdrawalCredited fires.
        vm.expectEmit(true, false, false, true, address(a));
        emit ISessionAuction.WithdrawalCredited(winner, owed);
        vm.prank(winner);
        a.withdrawRefund(LOT);

        assertEq(uint256(a.getLot(LOT).escrowAmount), 0, "G: escrow not zeroed on parked ERC-20 refund");
        assertEq(a.pendingWithdrawal(winner), owed, "G: ERC-20 amount not parked");

        // Toggle the token to succeed; claimPending pays the parked amount and emits WithdrawalClaimed.
        ftoken.setFail(false);
        uint256 balBefore = ftoken.balanceOf(winner);
        vm.expectEmit(true, false, false, true, address(a));
        emit ISessionAuction.WithdrawalClaimed(winner, owed);
        vm.prank(winner);
        a.claimPending();
        assertEq(ftoken.balanceOf(winner) - balBefore, owed, "G: ERC-20 claimPending did not pay");
        assertEq(a.pendingWithdrawal(winner), 0, "G: ERC-20 pending not cleared");
    }

    /// Escrow single-exit ordering: whichever of {withdrawRefund step 2, _release} runs first zeroes
    /// lot.escrowAmount; the loser of the race reverts, so the escrow pays out at most once. Here the
    /// session-void pull runs first (lot -> Refunded, escrow 0), so the subsequent releaseAfterWindow
    /// loses.
    ///
    /// The escrow-paying entrypoints (releaseAfterWindow, reclaimUndelivered, resolveDispute) check
    /// phase/deliveryState before reaching the internal escrowAmount==0 -> NoEscrow guard, so after a
    /// void-pull drives the lot to Refunded the phase guard (WrongDeliveryState) is what surfaces, both
    /// for this _release leg and for the _refund leg in test_WithdrawRefundDisputeBondToOpener.
    function test_EscrowSingleExitVoidThenRelease() external {
        _driveToDeliveredNative(); // Delivered: the lot is releasable via releaseAfterWindow

        vm.prank(address(hammer));
        auction.voidSession("void");

        // Session-void exit runs first: winner pulls free + escrow, lot -> Refunded, escrow == 0.
        _assertWinnerEscrowExit(LOT, winner, WIN_SLACK, WIN_BID);

        // The _release exit now loses: the lot is Refunded (no longer Delivered), so
        // releaseAfterWindow reverts WrongDeliveryState before it could re-pay the spent escrow.
        Lot memory l = auction.getLot(LOT);
        vm.warp(uint256(l.deliveredAt) + DISPUTE_WINDOW_SEC + 1);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.releaseAfterWindow(LOT);
    }

    /// Escrow single-exit ordering, reverse direction: a dispute-resolution terminal exit runs first and
    /// zeroes escrowAmount, then voidSession fires and the winner's withdrawRefund step 2 must be a safe
    /// no-op. Mirrors test_WithdrawRefundWinnerEscrowZeroIsNoOp but for the _refund terminal
    /// (resolveDispute RefundToBuyer) instead of the _release terminal. The buyer (highBidder) got their
    /// escrow back from the arbiter; under the later void the same buyer's withdrawRefund returns only
    /// residual free, emits no Refunded, and does not re-drive the terminal.
    function test_RefundThenVoidWinnerEscrowZeroIsNoOp() external {
        _driveToDisputedNative(seller); // Disputed, opener == seller, escrow == WIN_BID, winner is highBidder

        // Arbiter refunds the buyer first: _refund zeroes escrowAmount and drives the lot to Refunded.
        // Opener was the seller and the resolution is RefundToBuyer, so the bond also goes to the buyer
        // (the honest party): the buyer's gain is escrow + bond. After this both escrow and bond are 0.
        uint256 buyerBefore = winner.balance;
        vm.prank(arbiter);
        auction.resolveDispute(LOT, Resolution.RefundToBuyer, keccak256("photo"));
        assertEq(
            winner.balance - buyerBefore,
            uint256(WIN_BID) + uint256(DISPUTE_BOND_AMT),
            "_refund did not pay buyer escrow + bond"
        );

        Lot memory pre = auction.getLot(LOT);
        assertEq(uint256(pre.escrowAmount), 0, "_refund did not zero escrow (precondition)");
        assertEq(uint256(pre.disputeBond), 0, "resolveDispute did not zero the bond (precondition)");
        assertEq(pre.phase, uint8(LotPhase.Refunded), "lot not Refunded after _refund (precondition)");
        uint8 phaseBefore = pre.phase;
        uint8 dsBefore = pre.deliveryState;

        // Void after the terminal _refund.
        vm.prank(address(hammer));
        auction.voidSession("void-after-refund");

        // Escrow and bond were already returned by the arbiter; what remains for the winner is its
        // deposit slack (WIN_SLACK), which _refund never touched. So step 1 pays the slack and step 2 is
        // a no-op (escrow already 0): no Refunded, no terminal re-drive.
        uint256 balBefore = winner.balance;
        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.DepositWithdrawn(LOT, winner, WIN_SLACK);
        vm.prank(winner);
        auction.withdrawRefund(LOT);
        assertEq(winner.balance - balBefore, WIN_SLACK, "post-refund void pull paid != residual slack");

        Lot memory post = auction.getLot(LOT);
        assertEq(uint256(post.escrowAmount), 0, "escrow changed by no-op step 2 on Refunded terminal");
        assertEq(post.phase, phaseBefore, "Refunded terminal phase re-driven by no-op step 2");
        assertEq(post.deliveryState, dsBefore, "Refunded terminal deliveryState re-driven by no-op step 2");

        // A second pull now has nothing -> NothingToWithdraw (no double-pay, no spurious Refunded).
        vm.prank(winner);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(LOT);
    }

    /// voidSession idempotency. A second voidSession by the hammer is a harmless re-set (the flag is
    /// already true): it re-emits SessionVoided and does not alter subsequent withdrawRefund behavior.
    /// Safe to retry (a panic button may be hit twice).
    function test_VoidSessionIdempotent() external {
        _hammeredWinnerNative(); // LOT Hammered, escrow == WIN_BID, winner free == WIN_SLACK

        // First void.
        vm.expectEmit(true, false, false, true, address(auction));
        emit ISessionAuction.SessionVoided(SESSION_ID, "void-1");
        vm.prank(address(hammer));
        auction.voidSession("void-1");

        // Second void (already voided): a harmless re-set; re-emits with the new reason, no revert.
        vm.expectEmit(true, false, false, true, address(auction));
        emit ISessionAuction.SessionVoided(SESSION_ID, "void-2");
        vm.prank(address(hammer));
        auction.voidSession("void-2");

        // Subsequent withdrawRefund still behaves exactly as a single-void: the winner recovers
        // free + escrow in one pull, Refunded fires, escrow zeroed, a re-pull is NothingToWithdraw.
        _assertWinnerEscrowExit(LOT, winner, WIN_SLACK, WIN_BID);
    }

    /// voidSession with terminal lots already present: the void must leave already-terminal lots
    /// untouched; only escrowAmount!=0 lots get the step-2 exit. Build a Settled lot (escrow already
    /// released, escrow==0) and a NoSale lot (no bid), fire voidSession, and assert
    /// (a) both terminals keep their phase and zero escrow; (b) the Settled lot's highBidder pull is a
    /// step-1-only no-op (its remaining slack, no Refunded); (c) the NoSale lot's would-be bidder has
    /// nothing -> NothingToWithdraw.
    function test_VoidSessionWithTerminalLotsUntouched() external {
        // LOT -> Settled via the full happy path (winner confirms receipt). escrow == 0, phase Settled.
        _driveToReleasedNative();
        Lot memory settledBefore = auction.getLot(LOT);
        assertEq(settledBefore.phase, uint8(LotPhase.Settled), "precondition: LOT not Settled");
        assertEq(uint256(settledBefore.escrowAmount), 0, "precondition: Settled escrow != 0");

        // LOT2 -> NoSale: opened, no bid, hammered past endsAt. No escrow ever; terminal.
        _openLotWithReserve(LOT2, RESERVE_PRICE);
        vm.warp(block.timestamp + 2 days);
        auction.hammer(LOT2);
        Lot memory noSaleBefore = auction.getLot(LOT2);
        assertEq(noSaleBefore.phase, uint8(LotPhase.NoSale), "precondition: LOT2 not NoSale");
        assertEq(uint256(noSaleBefore.escrowAmount), 0, "precondition: NoSale escrow != 0");

        // Fire the session void with both terminals present.
        vm.prank(address(hammer));
        auction.voidSession("void-with-terminals");

        // (a) terminals are untouched: phase and escrow unchanged (the void did not re-drive them).
        Lot memory settledAfter = auction.getLot(LOT);
        assertEq(settledAfter.phase, uint8(LotPhase.Settled), "Settled lot phase re-driven by void");
        assertEq(uint256(settledAfter.escrowAmount), 0, "Settled lot escrow changed by void");
        Lot memory noSaleAfter = auction.getLot(LOT2);
        assertEq(noSaleAfter.phase, uint8(LotPhase.NoSale), "NoSale lot phase re-driven by void");
        assertEq(uint256(noSaleAfter.escrowAmount), 0, "NoSale lot escrow changed by void");

        // (b) the Settled lot's highBidder (winner) still holds its deposit slack (_release paid the
        //     seller from escrow but never touched the slack). The void pull returns exactly that slack
        //     via step 1, step 2 a no-op (escrow already 0): DepositWithdrawn(WIN_SLACK), no Refunded,
        //     no re-drive of the Settled terminal.
        uint256 balBefore = winner.balance;
        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.DepositWithdrawn(LOT, winner, WIN_SLACK);
        vm.prank(winner);
        auction.withdrawRefund(LOT);
        assertEq(winner.balance - balBefore, WIN_SLACK, "Settled-terminal void pull paid != residual slack");
        Lot memory settledPull = auction.getLot(LOT);
        assertEq(settledPull.phase, uint8(LotPhase.Settled), "Settled terminal re-driven by no-op step 2 pull");
        assertEq(uint256(settledPull.escrowAmount), 0, "Settled escrow changed by no-op step 2 pull");

        // A second winner pull is now empty -> NothingToWithdraw (slack already taken, escrow still 0).
        vm.prank(winner);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(LOT);

        // (c) the NoSale lot has no bidder/escrow: any caller has nothing -> NothingToWithdraw.
        vm.prank(relayer);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(LOT2);
    }

    /// Reentrancy guard on the step-1-only (deposit-refund) push. The other reentrancy test re-enters on
    /// the step-2 escrow push; this one lands the attacker as an outbid loser (no escrow) so the
    /// re-entered _pay is the step-1 deposit refund, asserting the same guard + single-park outcome on
    /// that path.
    function test_WithdrawRefundReentryLoserStep1Blocked() external {
        _initNative();
        _openLot(LOT);

        // The attacker bids first (LOSE_BID), then `winner` outbids it, so the attacker is an outbid
        // loser holding free == LOSE_DEPOSIT, not highBidder, and its withdrawRefund is step-1 only. The
        // attacker is an ERC-1271 contract whose bid authorizes via isValidSignature recovering to
        // `loser`, so bind loserKey for the envelope signature.
        G_ReentrantRefund attacker = new G_ReentrantRefund(auction, LOT, loser);
        _bindKey(address(attacker), loserKey);
        vm.deal(address(attacker), LOSE_DEPOSIT + 1 ether);
        _mockPaddle(address(attacker), PADDLE_LOSER);
        vm.prank(address(attacker));
        auction.depositCeiling{value: LOSE_DEPOSIT}(LOT, LOSE_DEPOSIT);
        _placeBidFor(address(attacker), 0, LOSE_BID, PADDLE_LOSER, 0);

        // winner outbids the attacker (attacker committed -> free; no longer top).
        _depositNative(winner, WIN_DEPOSIT);
        _placeBidFor(winner, 0, WIN_BID, PADDLE_WINNER, LOSE_BID);
        _hammer(LOT); // highBidder == winner; attacker holds free == LOSE_DEPOSIT, no escrow

        vm.prank(address(hammer));
        auction.voidSession("void");

        uint256 owed = LOSE_DEPOSIT; // free+committed only (the attacker is a loser)

        // The step-1 _pay pushes to the attacker, whose receive() re-enters; the guard makes the inner
        // call revert, the attacker swallows + records it, and the outer push pays directly once.
        uint256 attackerBefore = address(attacker).balance;
        attacker.arm();
        vm.prank(address(attacker));
        auction.withdrawRefund(LOT);

        // (a) the inner re-entry happened and reverted with the OZ guard selector (readable only because
        //     the attacker returns after capturing it).
        assertTrue(attacker.reentered(), "G: step-1 re-entry was not attempted");
        assertEq(
            attacker.innerSelector(),
            ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector,
            "G: step-1 inner re-entry did not revert ReentrancyGuardReentrantCall"
        );

        // (b) no double-pay: free zeroed once, owed paid once, nothing parked, and the winner's escrow is
        //     untouched (the step-1-only push cannot cross into it).
        assertEq(auction.withdrawableFree(LOT, address(attacker)), 0, "G: loser free not zeroed under blocked re-entry");
        assertEq(address(attacker).balance - attackerBefore, owed, "G: loser not paid exactly owed once");
        assertEq(auction.pendingWithdrawal(address(attacker)), 0, "G: step-1 nothing should be parked (push accepted)");
        assertEq(
            uint256(auction.getLot(LOT).escrowAmount), uint256(WIN_BID), "G: loser re-entry reached the winner escrow"
        );

        // (c) single-exit: a SECOND withdrawRefund is now empty -> NothingToWithdraw (the deposit was
        //     consumed exactly once; no residual second extraction survived the blocked re-entry).
        vm.prank(address(attacker));
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(LOT);
    }

    /// Pull-exit survives a simultaneously paused-and-voided session (the realistic incident response is
    /// pause() + voidSession() together). withdrawRefund is intentionally not whenNotPaused
    /// (ISessionAuction declares it plain external), so the no-strand guarantee holds while paused: the
    /// winner's full step-1+step-2 exit and claimPending both work.
    function test_WithdrawRefundUnderPauseAndVoid() external {
        _hammeredWinnerNative(); // LOT Hammered, escrow == WIN_BID, winner free == WIN_SLACK

        // Pause and void (the panic combo).
        vm.prank(pauser);
        auction.pause();
        assertTrue(auction.paused(), "clone should be paused");
        vm.prank(address(hammer));
        auction.voidSession("pause-and-void");

        // The full exit is reachable while paused (EnforcedPause would surface if a stray whenNotPaused
        // fronted the pull).
        _assertWinnerEscrowExit(LOT, winner, WIN_SLACK, WIN_BID);

        // claimPending is likewise not pause-gated: with nothing parked it reaches its body guard ->
        // NothingToWithdraw, never EnforcedPause.
        vm.prank(winner);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.claimPending();
    }

    /// Zero-slack winner boundary: the step-1 amount==0 guard runs after the steps 1-3 sum, so an
    /// escrow!=0 winner must not be short-circuited by a zero step-1. A winner whose deposit equals its
    /// bid has free == 0, committed == 0 post-hammer and escrowAmount == bid. The pull must still return
    /// exactly the escrow, emit DepositWithdrawn(escrow) + Refunded(escrow), and not revert
    /// NothingToWithdraw. Native rail.
    function test_WithdrawRefundZeroSlackWinnerEscrowOnly() external {
        _initNative();
        _openLotWithReserve(LOT, RESERVE_PRICE);

        // Deposit exactly the bid: no slack. Post-hammer free == 0, committed == 0, escrow == bid.
        _depositNative(winner, uint256(WIN_BID));
        _placeBidFor(winner, 0, WIN_BID, PADDLE_WINNER, 0);
        _hammer(LOT);

        assertEq(auction.withdrawableFree(LOT, winner), 0, "precondition: winner free != 0 (not zero-slack)");
        assertEq(uint256(auction.getLot(LOT).escrowAmount), uint256(WIN_BID), "precondition: escrow != bid");

        vm.prank(address(hammer));
        auction.voidSession("void");

        uint256 balBefore = winner.balance;

        // free == 0, escrow == WIN_BID: DepositWithdrawn carries exactly the escrow. The amount==0 guard
        // must not fire (it is checked after escrow is added).
        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.DepositWithdrawn(LOT, winner, uint256(WIN_BID));
        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.Refunded(LOT, winner, uint256(WIN_BID));
        vm.prank(winner);
        auction.withdrawRefund(LOT);

        assertEq(winner.balance - balBefore, uint256(WIN_BID), "zero-slack winner delta != escrow");
        Lot memory l = auction.getLot(LOT);
        assertEq(uint256(l.escrowAmount), 0, "zero-slack: escrow not zeroed");
        assertEq(l.phase, uint8(LotPhase.Refunded), "zero-slack: phase not Refunded");
        assertEq(l.deliveryState, uint8(DeliveryState.Refunded), "zero-slack: deliveryState not Refunded");

        // A second pull is now genuinely empty -> NothingToWithdraw (the single-exit re-pull guard).
        vm.prank(winner);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(LOT);
    }

    /// Dust-escrow boundary: a 1-wei winner escrow under a session void. With a 1-wei reserve and a
    /// 1-wei deposit==bid, the winner's escrowAmount is exactly 1 wei and free is 0. The pull must
    /// return exactly 1 wei, emit DepositWithdrawn(1) + Refunded(1), zero the escrow, and not revert.
    /// Proves the escrow exit has no implicit nonzero-dust floor and the step-1 amount==0 ordering
    /// holds at the smallest possible escrow. Native rail.
    function test_WithdrawRefundDustEscrow() external {
        _initNative();
        _openLotWithReserve(LOT, 1); // reserve == 1 wei, so a 1-wei deposit/bid is admissible

        _depositNative(winner, 1); // deposit == 1 wei (>= reserve), no slack
        _placeBidFor(winner, 0, 1, PADDLE_WINNER, 0); // bid == 1 wei
        _hammer(LOT);

        assertEq(uint256(auction.getLot(LOT).escrowAmount), 1, "precondition: dust escrow != 1 wei");

        vm.prank(address(hammer));
        auction.voidSession("void-dust");

        uint256 balBefore = winner.balance;

        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.DepositWithdrawn(LOT, winner, 1);
        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.Refunded(LOT, winner, 1);
        vm.prank(winner);
        auction.withdrawRefund(LOT);

        assertEq(winner.balance - balBefore, 1, "dust winner delta != 1 wei");
        assertEq(uint256(auction.getLot(LOT).escrowAmount), 0, "dust: escrow not zeroed");
        assertEq(auction.getLot(LOT).phase, uint8(LotPhase.Refunded), "dust: phase not Refunded");
    }

    // Shared assertion: the full winner-escrow exit, reused across every non-terminal phase.

    /// @dev Assert the winner-escrow no-strand exit on the default `auction`, native rail:
    ///        - one withdrawRefund returns free(`slack`) + escrow(`escrow`);
    ///        - emits DepositWithdrawn(lotId, who, slack+escrow) and Refunded(lotId, who, escrow);
    ///        - lot.escrowAmount == 0, phase == Refunded, deliveryState == Refunded;
    ///        - the clone-held balance falls by exactly slack+escrow (no leak, no strand);
    ///        - a second withdrawRefund reverts NothingToWithdraw (escrow paid once).
    ///      The {_release, _refund} losing-the-race legs are asserted in
    ///      test_EscrowSingleExitVoidThenRelease, where the pre-void deliveryState (and so the guard
    ///      selector) is fixed; this helper runs across phases where those guards differ, so it pins only
    ///      the NothingToWithdraw re-pull.
    function _assertWinnerEscrowExit(uint256 lotId, address who, uint128 slack, uint128 escrow) private {
        // Step 2 of withdrawRefund requires the voided flag, so void first. voidSession moves no funds.
        vm.prank(address(hammer));
        auction.voidSession("g-fund3b-no-strand");

        uint256 expected = uint256(slack) + uint256(escrow);
        uint256 balBefore = who.balance;

        // Held-side check: the contract balance must fall by exactly the amount paid. The payee delta and
        // post-state zeros alone do not pin the source: a step-2 that credits the payee but fails to
        // debit held (double-counts free, or pays escrow from a mis-accounted slot) would pass them.
        // `who` is always a plain EOA distinct from the clone in every caller.
        uint256 heldBefore = address(auction).balance;

        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.DepositWithdrawn(lotId, who, expected);
        vm.expectEmit(true, true, false, true, address(auction));
        emit ISessionAuction.Refunded(lotId, who, uint256(escrow));
        vm.prank(who);
        auction.withdrawRefund(lotId);

        assertEq(who.balance - balBefore, expected, "winner delta != free + escrow");

        // Held side drops by exactly free+escrow on the winner pull.
        assertEq(
            heldBefore - address(auction).balance,
            expected,
            "clone-held delta != free+escrow on winner pull (leak/strand)"
        );

        Lot memory l = auction.getLot(lotId);
        assertEq(uint256(l.escrowAmount), 0, "escrowAmount not zeroed");
        assertEq(l.phase, uint8(LotPhase.Refunded), "phase not Refunded");
        assertEq(l.deliveryState, uint8(DeliveryState.Refunded), "deliveryState not Refunded");

        // Second pull: deposit + escrow already zeroed -> NothingToWithdraw.
        vm.prank(who);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        auction.withdrawRefund(lotId);
    }

    // Private pre-state builders (real entrypoints).

    // Session bring-up (native, the default `auction`).
    function _initNative() private {
        vm.prank(address(hammer));
        auction.initialize(_defaultInitConfig(address(0)));
        vm.prank(address(hammer));
        auction.registerOperatorKey(keccak256("OPERATOR_QX_FIXTURE"), keccak256("OPERATOR_QY_FIXTURE"));
    }

    function _openLot(uint256 lotId) private {
        vm.prank(address(hammer));
        auction.openLot(lotId, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));
    }

    /// @dev Open `lotId` on the default `auction` with an explicit `reserve` (for the dust-escrow and
    ///      zero-slack boundary cases that need a reserve below the default to admit a tiny bid).
    function _openLotWithReserve(uint256 lotId, uint96 reserve) private {
        vm.prank(address(hammer));
        auction.openLot(lotId, seller, reserve, uint64(block.timestamp + 1 days));
    }

    function _hammer(uint256 lotId) private {
        vm.warp(block.timestamp + 2 days); // past endsAt
        auction.hammer(lotId);
    }

    // Deposits.
    function _depositNative(address principal, uint256 amount) private {
        _depositNativeLot(principal, LOT, amount);
    }

    /// @dev Deposit native into an arbitrary lotId on the default `auction` (lot-parameterized twin of
    ///      _depositNative, which hardcodes LOT).
    function _depositNativeLot(address principal, uint256 lotId, uint256 amount) private {
        vm.prank(principal);
        auction.depositCeiling{value: amount}(lotId, amount);
    }

    // Paddle mock: placeBid reads only paddleOf, and PaddleRegistry.paddleOf is a stub here, so mock a
    // nonzero KYC paddle. FlagRegistry is irrelevant to the void path.
    function _mockPaddle(address principal, uint16 paddleId) private {
        vm.mockCall(
            address(paddles), abi.encodeWithSelector(IPaddleRegistry.paddleOf.selector, principal), abi.encode(paddleId)
        );
    }

    // Make the flag verifiers answer the voidAndAward happy case (offender FLAGGED, promoted clean).
    function _mockFlagsForVoidAndAward(uint16 offenderPaddle, uint16 cleanPaddle) private {
        vm.mockCall(address(flags), abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector), abi.encode(true));
        vm.mockCall(
            address(flags), abi.encodeWithSelector(IFlagRegistry.verifyNonMembership.selector), abi.encode(true)
        );
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyNonMembership.selector, SESSION_ID, offenderPaddle),
            abi.encode(false)
        );
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector, SESSION_ID, cleanPaddle),
            abi.encode(false)
        );
    }

    // Envelope / quote / placeBid builders.
    // The ceilingCommit hides the bid `amount` under bytes32("salt"); SessionAuction.reveal opens it
    // against keccak256(abi.encode(maxBid, salt)), so the commit must be over the actual bid amount
    // (every reveal site here opens with the bid amount + "salt"). A fixed-amount commit would reveal as
    // CommitmentMismatch on any lot whose bid differs.
    function _ceiling(address principal, uint256 lotId, uint128 amount) private view returns (Ceiling memory c) {
        c = Ceiling({
            principal: principal,
            sessionId: SESSION_ID,
            lotId: lotId,
            ceilingCommit: keccak256(abi.encode(amount, bytes32("salt"))),
            strategy: 0,
            deadline: uint64(block.timestamp + 1 days),
            maxBids: 16,
            nonceKey: uint192(uint256(keccak256(abi.encode(SESSION_ID, lotId, principal))))
        });
    }

    function _operatorKeyId() private view returns (bytes32) {
        return _baseOperatorKeyId();
    }

    function _signCeiling(address clone, Ceiling memory c, uint256 signerKey) private view returns (bytes memory) {
        bytes32 structHash = keccak256(
            abi.encode(
                CEILING_TYPEHASH, c.principal, c.sessionId, c.lotId,
                c.ceilingCommit, c.strategy, c.deadline, c.maxBids, c.nonceKey
            )
        );
        bytes32 domainSep = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256(bytes("Hammer")),
                keccak256(bytes("1")),
                block.chainid,
                clone
            )
        );
        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", domainSep, structHash));
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(signerKey, digest);
        return abi.encodePacked(r, s, v);
    }

    /// @dev Place a bid on the default `auction` (LOT) from `principal` (principal == submitter).
    function _placeBidNative(address principal, uint64 bidIndex, uint128 amount, uint16 paddleId, uint128 prevTop)
        private
    {
        _placeBidFor(principal, bidIndex, amount, paddleId, prevTop);
    }

    /// @dev Place a bid on the default `auction` for `principal`, submitted by `principal`.
    function _placeBidFor(address principal, uint64 bidIndex, uint128 amount, uint16 paddleId, uint128 prevTop)
        private
    {
        _mockPaddle(principal, paddleId);
        Ceiling memory c = _ceiling(principal, LOT, amount);
        uint256 signerKey = _signerKeyFor(principal);
        bytes memory sig = _signCeiling(address(auction), c, signerKey);
        AttestationQuote memory q = _realQuote(c, LOT, amount, bidIndex, prevTop, keccak256(abi.encode(principal, bidIndex, LOT)));
        vm.prank(principal);
        auction.placeBid(c, LOT, principal, bidIndex, amount, sig, _baseOperatorKeyId(), q);
    }

    /// @dev Place a bid on the default `auction` for `principal` and return the per-lot bid seq the
    ///      contract assigned it. voidAndAward's candidate must carry the promoted bidder's own seq
    ///      (the heap stores it, _verifyAndPromote matches on it); the offender's lot.winnerSeq yields
    ///      BadCandidate. There is no seq getter, so capture it from the BidPlaced event.
    function _placeBidForCapturingSeq(
        address principal,
        uint64 bidIndex,
        uint128 amount,
        uint16 paddleId,
        uint128 prevTop
    ) private returns (uint64 seq) {
        vm.recordLogs();
        _placeBidFor(principal, bidIndex, amount, paddleId, prevTop);
        Vm.Log[] memory logs = vm.getRecordedLogs();
        bytes32 t1 = bytes32(LOT);
        bytes32 t2 = bytes32(uint256(uint160(principal)));
        for (uint256 i = 0; i < logs.length; i++) {
            Vm.Log memory lg = logs[i];
            if (lg.emitter != address(auction) || lg.topics.length < 3) continue;
            if (lg.topics[0] != BID_PLACED_SIG || lg.topics[1] != t1 || lg.topics[2] != t2) continue;
            (, uint64 emittedSeq) = abi.decode(lg.data, (uint128, uint64));
            return emittedSeq;
        }
        revert("no matching BidPlaced in recorded logs");
    }

    /// @dev Place a bid on the default `auction` for `principal` on an arbitrary lotId (lot-parameterized
    ///      twin of _placeBidFor). The ceiling and quote are keyed on `lotId` so each lot gets an
    ///      independent nonceKey.
    function _placeBidForLot(
        address principal,
        uint256 lotId,
        uint64 bidIndex,
        uint128 amount,
        uint16 paddleId,
        uint128 prevTop
    ) private {
        _mockPaddle(principal, paddleId);
        Ceiling memory c = Ceiling({
            principal: principal,
            sessionId: SESSION_ID,
            lotId: lotId,
            ceilingCommit: keccak256(abi.encode(amount, bytes32("salt"))),
            strategy: 0,
            deadline: uint64(block.timestamp + 1 days),
            maxBids: 16,
            nonceKey: uint192(uint256(keccak256(abi.encode(SESSION_ID, lotId, principal))))
        });
        uint256 signerKey = _signerKeyFor(principal);
        bytes memory sig = _signCeiling(address(auction), c, signerKey);
        AttestationQuote memory q = _realQuote(c, lotId, amount, bidIndex, prevTop, keccak256(abi.encode(principal, bidIndex, lotId)));
        vm.prank(principal);
        auction.placeBid(c, lotId, principal, bidIndex, amount, sig, _baseOperatorKeyId(), q);
    }

    /// @dev Place a bid on an arbitrary clone `a` for `principal` on LOT (ERC-20 / mixed helpers).
    ///      Mirrors _placeBidFor but targets `a`.
    function _placeBidOn(
        SessionAuction a,
        address principal,
        uint64 bidIndex,
        uint128 amount,
        uint16 paddleId,
        uint128 prevTop
    ) private {
        _mockPaddle(principal, paddleId);
        Ceiling memory c = Ceiling({
            principal: principal,
            sessionId: SESSION_ID,
            lotId: LOT,
            ceilingCommit: keccak256(abi.encode(amount, bytes32("salt"))),
            strategy: 0,
            deadline: uint64(block.timestamp + 1 days),
            maxBids: 16,
            nonceKey: uint192(uint256(keccak256(abi.encode(SESSION_ID, LOT, principal))))
        });
        uint256 signerKey = _signerKeyFor(principal);
        bytes memory sig = _signCeiling(address(a), c, signerKey);
        AttestationQuote memory q = _realQuote(c, LOT, amount, bidIndex, prevTop, keccak256(abi.encode(principal, bidIndex, LOT)));
        vm.prank(principal);
        a.placeBid(c, LOT, principal, bidIndex, amount, sig, _baseOperatorKeyId(), q);
    }

    // Composite native pre-states for the winner (LOT).

    /// @dev LOT Hammered with `winner` as provisional winner: escrowAmount == WIN_BID, winner
    ///      Deposit == {free: WIN_SLACK, committed: 0}.
    function _hammeredWinnerNative() private {
        _initNative();
        _openLot(LOT);
        _depositNative(winner, WIN_DEPOSIT);
        _placeBidNative(winner, 0, WIN_BID, PADDLE_WINNER, 0);
        _hammer(LOT);
    }

    /// @dev LOT Voided with the promoted winner == `winner`: an offender (higher, flagged) is voided and
    ///      `winner` (clean, lower) promoted, re-locking its own WIN_BID into escrowAmount and keeping
    ///      WIN_SLACK free. The offender forfeited its escrow to Treasury (not held here).
    function _votedPromotedWinnerNative() private {
        _initNative();
        _openLot(LOT);

        address offender = makeAddr("g_offender_for_void");
        fundEth(offender, INITIAL_ETH);

        // promoted-clean bidder (`winner`) bids first (lower), offender bids higher and tops.
        _depositNative(winner, WIN_DEPOSIT);
        vm.prank(offender);
        auction.depositCeiling{value: WIN_DEPOSIT}(LOT, WIN_DEPOSIT);

        // Capture the promoted winner's own bid seq: voidAndAward's candidate matches the heap slot on
        // (bidder, amount, paddleId, seq), and the promoted slot carries the winner's seq, not the
        // offender's lot.winnerSeq (-> BadCandidate).
        uint64 promotedSeq = _placeBidForCapturingSeq(winner, 0, WIN_BID, PADDLE_PROMOTED, 0);
        _placeBidFor(offender, 0, OFFENDER_BID, PADDLE_OFFENDER, WIN_BID); // offender tops at higher
        _hammer(LOT); // offender is provisional winner; offender escrow == OFFENDER_BID

        // At hammer the offender's larger bid is locked into escrowAmount, so escrowAmount ==
        // OFFENDER_BID before the promote replaces it.
        assertEq(
            uint256(auction.getLot(LOT).escrowAmount), uint256(OFFENDER_BID), "pre-void escrow != offender bid"
        );

        // void the flagged offender and promote `winner` (re-locks winner's own WIN_BID into escrow).
        _mockFlagsForVoidAndAward(PADDLE_OFFENDER, PADDLE_PROMOTED);
        bytes32[] memory inclusion = _membershipProof(PADDLE_OFFENDER);
        NextCleanCandidate memory cand = _promotedCandidate(winner, WIN_BID, PADDLE_PROMOTED, uint40(promotedSeq));
        vm.prank(relayer); // permissionless
        auction.voidAndAward(LOT, inclusion, cand);

        // No-strand: voidAndAward must have captured and zeroed the offender's escrow and re-locked the
        // slot to the promoted bid (WIN_BID), not left the larger offender escrow (which would over-pay
        // the promoted-winner pull). Paired with the offender free-slack check below for conservation.
        assertEq(
            uint256(auction.getLot(LOT).escrowAmount),
            uint256(WIN_BID),
            "post-void escrow != promoted bid (offender escrow not captured/re-locked)"
        );
        // The offender is no longer highBidder; its committed was zeroed at hammer (escrow, then
        // forfeited), so only its deposit slack above OFFENDER_BID remains free.
        assertEq(auction.getLot(LOT).highBidder, winner, "highBidder not the promoted winner");
        assertEq(
            auction.withdrawableFree(LOT, offender),
            WIN_DEPOSIT - uint256(OFFENDER_BID),
            "offender free != deposit slack above its forfeited bid"
        );
    }

    /// @dev LOT Hammered with a flagged offender (PADDLE_OFFENDER, OFFENDER_BID) on top and the clean
    ///      `winner` (PADDLE_PROMOTED, WIN_BID) below in the heap, with no voidAndAward run yet (the
    ///      pre-promotion state of _votedPromotedWinnerNative; offender escrow == OFFENDER_BID). Returns
    ///      the offender address and the promoted winner's own bid seq (the voidAndAward candidate.seq).
    function _hammeredFlaggedOffenderNative() private returns (address offender, uint64 promotedSeq) {
        _initNative();
        _openLot(LOT);

        offender = makeAddr("g_offender_for_void");
        fundEth(offender, INITIAL_ETH);

        // promoted-clean bidder (`winner`) bids first (lower), offender bids higher and tops.
        _depositNative(winner, WIN_DEPOSIT);
        vm.prank(offender);
        auction.depositCeiling{value: WIN_DEPOSIT}(LOT, WIN_DEPOSIT);

        // Capture the promoted winner's own bid seq (the heap matches voidAndAward on it).
        promotedSeq = _placeBidForCapturingSeq(winner, 0, WIN_BID, PADDLE_PROMOTED, 0);
        _placeBidFor(offender, 0, OFFENDER_BID, PADDLE_OFFENDER, WIN_BID); // offender tops at higher
        _hammer(LOT); // offender is provisional winner; offender escrow == OFFENDER_BID

        // The offender's larger bid sits in escrowAmount post-hammer, before any promote.
        assertEq(
            uint256(auction.getLot(LOT).escrowAmount),
            uint256(OFFENDER_BID),
            "pre-void escrow != offender bid (still-Hammered fixture)"
        );
    }

    /// @dev LOT Awaiting / AwaitingDelivery with `winner`, escrow == WIN_BID. Path:
    ///      hammer -> reveal -> finalizeWinner (AC window closed).
    function _driveToAwaitingNative() private {
        _hammeredWinnerNative();
        uint64 wseq = auction.getLot(LOT).winnerSeq;
        vm.prank(winner);
        auction.reveal(LOT, wseq, WIN_BID, bytes32("salt"));
        Lot memory l = auction.getLot(LOT);
        vm.warp(uint256(l.hammeredAt) + AC_CHALLENGE_SEC + 1);
        auction.finalizeWinner(LOT);
    }

    /// @dev LOT Delivered (seller marked delivered), escrow == WIN_BID.
    function _driveToDeliveredNative() private {
        _driveToAwaitingNative();
        vm.prank(seller);
        auction.markDelivered(LOT, keccak256("proof"), "ipfs://proof");
    }

    /// @dev LOT Disputed with `opener` (buyer == winner, or seller) holding DISPUTE_BOND_AMT,
    ///      escrow == WIN_BID, deliveryState == Disputed.
    function _driveToDisputedNative(address opener) private {
        _driveToAwaitingNative();
        vm.deal(opener, opener.balance + uint256(DISPUTE_BOND_AMT));
        vm.prank(opener);
        auction.openDispute{value: DISPUTE_BOND_AMT}(LOT, keccak256("claim"));
    }

    /// @dev LOT Settled / Released (escrow paid to seller, escrowAmount == 0), winner free == WIN_SLACK.
    ///      Path: Delivered -> confirmReceipt (buyer == winner) -> Released.
    function _driveToReleasedNative() private {
        _driveToDeliveredNative();
        vm.prank(winner); // the buyer (highBidder)
        auction.confirmReceipt(LOT, keccak256("photo"), "ipfs://photo");
    }

    // Signer-key resolver.
    // Map a bid principal to the key whose signature authorizes its ceiling envelope. For an EOA the
    // principal is the recovered signer (ECDSA branch of SignatureChecker). For a contract principal
    // (the G_ ERC-1271 bidders) the envelope is signed with the contract's owner key, which
    // isValidSignature recovers to, registered via _bindKey at deploy time. The named-EOA arms cover
    // every named EOA; the _boundKey map covers every contract bidder.
    function _signerKeyFor(address principal) private returns (uint256) {
        if (principal == winner) return winnerKey;
        if (principal == loser) return loserKey;
        if (principal == loser2) return loser2Key;
        if (principal == winner2) return winner2Key;
        if (principal == makeAddr("g_offender_for_void")) return offenderKey;
        uint256 bound = _boundKey[principal];
        if (bound != 0) return bound;
        revert("_signerKeyFor: principal not bound");
    }

    /// @dev Bind a signer key to a contract principal so _signerKeyFor resolves it (the contract's
    ///      isValidSignature recovers to `key`'s address, so the envelope is signed with `key`).
    function _bindKey(address principal, uint256 key) private {
        _boundKey[principal] = key;
    }

    // voidAndAward proof / candidate builders (boundary-leaf proof layout).
    function _membershipProof(uint16 paddle) private pure returns (bytes32[] memory proof) {
        proof = new bytes32[](3);
        proof[0] = bytes32(uint256(paddle)); // low == paddle (membership)
        proof[1] = bytes32(uint256(paddle) + 1); // high
        proof[2] = keccak256(abi.encode("sibling"));
    }

    function _nonMembershipProof(uint16 paddle) private pure returns (bytes32[] memory proof) {
        proof = new bytes32[](3);
        proof[0] = bytes32(uint256(paddle) - 1); // low < paddle
        proof[1] = bytes32(uint256(paddle) + 1); // high > paddle (brackets it)
        proof[2] = keccak256(abi.encode("sibling"));
    }

    /// @dev A promotion candidate for the in-storage heap. With min-replace insertion and only two
    ///      distinct paddles, the promoted bidder sits at slot 0 (first inserted) and the offender at
    ///      slot 1; the ONE strictly-higher slot is the offender, so one preceding-flag-inclusion proof.
    function _promotedCandidate(address bidder, uint128 amount, uint16 paddleId, uint40 seq)
        private
        pure
        returns (NextCleanCandidate memory c)
    {
        bytes32[][] memory preceding = new bytes32[][](1);
        preceding[0] = _membershipProof(PADDLE_OFFENDER); // the one strictly-higher slot is flagged
        c = NextCleanCandidate({
            heapIndex: 0,
            bidder: bidder,
            amount: amount,
            paddleId: paddleId,
            seq: seq,
            flagNonMembership: _nonMembershipProof(paddleId),
            precedingFlagInclusion: preceding
        });
    }

    // Mixed-session builder + conservation helpers (rail-parameterized).

    /// @dev Build a mixed session on a fresh clone for `payToken`:
    ///        LOT  : winner (deposit WIN_DEPOSIT, bid WIN_BID, wins, escrow == WIN_BID) +
    ///               loser (deposit LOSE_DEPOSIT, bid LOSE_BID, outbid, free == whole deposit).
    ///        LOT2 : winner2 (deposit WIN_DEPOSIT, bid WIN_BID, wins, escrow == WIN_BID) +
    ///               loser2 (deposit LOSE_DEPOSIT, bid LOSE_BID, outbid by winner2). loser2 is a genuine
    ///               loser-only bucket: never LOT2's highBidder, never holds escrow, so its void pull is
    ///               step-1 only (free+committed) and emits only DepositWithdrawn.
    ///        LOT3 : winner (deposit WIN_DEPOSIT, bid WIN_BID, wins, escrow == WIN_BID) then a dispute
    ///               opened by the winner (bond DISPUTE_BOND_AMT) -> Disputed.
    ///      `winner` is reused across LOT and LOT3 with per-lot nonceKeys, so its deposits/escrows/bond
    ///      are independent. Returns the clone.
    function _mixedSession(address payToken) private returns (SessionAuction a) {
        a = SessionAuction(Clones.clone(address(impl)));
        vm.prank(address(hammer));
        a.initialize(_defaultInitConfig(payToken));
        vm.prank(address(hammer));
        a.registerOperatorKey(keccak256("OPERATOR_QX_FIXTURE"), keccak256("OPERATOR_QY_FIXTURE"));

        uint256 winDeposit = payToken == address(0) ? WIN_DEPOSIT : WIN_DEPOSIT_T;
        uint128 winBid = payToken == address(0) ? WIN_BID : WIN_BID_T;
        uint256 loseDeposit = payToken == address(0) ? LOSE_DEPOSIT : LOSE_DEPOSIT_T;
        uint128 loseBid = payToken == address(0) ? LOSE_BID : LOSE_BID_T;
        // Rail-scaled reserve: the native lots clear at RESERVE_PRICE (1e18, below the 10/60-ether bids),
        // the ERC-20 lots at RESERVE_PRICE_T (1e6, below the 10e6/60e6 token bids). A single RESERVE_PRICE
        // for both rails would reject every 6-decimal token bid as BidTooLow.
        uint96 reserve = payToken == address(0) ? RESERVE_PRICE : RESERVE_PRICE_T;

        // Open the three lots.
        for (uint256 i = 1; i <= 3; i++) {
            vm.prank(address(hammer));
            a.openLot(i, seller, reserve, uint64(block.timestamp + 1 days));
        }

        // LOT: winner beats loser.
        _fundDeposit(a, payToken, winner, LOT, winDeposit);
        _fundDeposit(a, payToken, loser, LOT, loseDeposit);
        _bidOnLot(a, payToken, loser, LOT, 0, loseBid, PADDLE_LOSER, 0);
        _bidOnLot(a, payToken, winner, LOT, 0, winBid, PADDLE_WINNER, loseBid);

        // LOT2: winner2 beats loser2 (loser2 is a genuine loser-only bucket). loser2 bids first, then
        // winner2 outbids: at hammer winner2 is highBidder (escrow == WIN_BID) and loser2's committed
        // moved back to free, so loser2 holds free == LOSE_DEPOSIT and is never highBidder (step-1-only
        // void pull).
        _fundDeposit(a, payToken, loser2, LOT2, loseDeposit);
        _fundDeposit(a, payToken, winner2, LOT2, winDeposit);
        _bidOnLot(a, payToken, loser2, LOT2, 0, loseBid, PADDLE_L2, 0);
        _bidOnLot(a, payToken, winner2, LOT2, 0, winBid, PADDLE_W2, loseBid);

        // LOT3: winner wins, then opens a dispute (Disputed; opener == winner).
        _fundDeposit(a, payToken, winner, LOT3, winDeposit);
        _bidOnLot(a, payToken, winner, LOT3, 0, winBid, PADDLE_WINNER, 0);

        // Close + hammer all three.
        vm.warp(block.timestamp + 2 days);
        a.hammer(LOT);
        a.hammer(LOT2);
        a.hammer(LOT3);

        // drive LOT3 to Disputed via reveal -> finalize -> openDispute (opener == winner).
        // Read winnerSeq into a local before vm.prank: an inline a.getLot(...) argument would consume the
        // prank, so reveal would run as the test contract and revert NotPrincipal.
        uint64 wseq3 = a.getLot(LOT3).winnerSeq;
        vm.prank(winner);
        a.reveal(LOT3, wseq3, winBid, bytes32("salt"));
        Lot memory l3 = a.getLot(LOT3);
        vm.warp(uint256(l3.hammeredAt) + AC_CHALLENGE_SEC + 1);
        a.finalizeWinner(LOT3);
        _openDisputeOn(a, payToken, winner, LOT3);
    }

    function _fundDeposit(SessionAuction a, address payToken, address principal, uint256 lotId, uint256 amount)
        private
    {
        if (payToken == address(0)) {
            vm.deal(principal, principal.balance + amount);
            vm.prank(principal);
            a.depositCeiling{value: amount}(lotId, amount);
        } else {
            MockERC20(payToken).mint(principal, amount);
            vm.prank(principal);
            MockERC20(payToken).approve(address(a), amount);
            vm.prank(principal);
            a.depositCeiling(lotId, amount);
        }
    }

    function _bidOnLot(
        SessionAuction a,
        address payToken,
        address principal,
        uint256 lotId,
        uint64 bidIndex,
        uint128 amount,
        uint16 paddleId,
        uint128 prevTop
    ) private {
        payToken; // rail does not change the bid envelope; deposits already differ per rail
        _mockPaddle(principal, paddleId);
        Ceiling memory c = Ceiling({
            principal: principal,
            sessionId: SESSION_ID,
            lotId: lotId,
            ceilingCommit: keccak256(abi.encode(amount, bytes32("salt"))),
            strategy: 0,
            deadline: uint64(block.timestamp + 1 days),
            maxBids: 16,
            nonceKey: uint192(uint256(keccak256(abi.encode(SESSION_ID, lotId, principal))))
        });
        uint256 signerKey = _signerKeyFor(principal);
        bytes memory sig = _signCeiling(address(a), c, signerKey);
        AttestationQuote memory q = _realQuote(c, lotId, amount, bidIndex, prevTop, keccak256(abi.encode(principal, bidIndex, lotId)));
        vm.prank(principal);
        a.placeBid(c, lotId, principal, bidIndex, amount, sig, _baseOperatorKeyId(), q);
    }

    function _openDisputeOn(SessionAuction a, address payToken, address opener, uint256 lotId) private {
        if (payToken == address(0)) {
            vm.deal(opener, opener.balance + uint256(DISPUTE_BOND_AMT));
            vm.prank(opener);
            a.openDispute{value: DISPUTE_BOND_AMT}(lotId, keccak256("claim"));
        } else {
            MockERC20(payToken).mint(opener, uint256(DISPUTE_BOND_AMT));
            vm.prank(opener);
            MockERC20(payToken).approve(address(a), uint256(DISPUTE_BOND_AMT));
            vm.prank(opener);
            a.openDispute(lotId, keccak256("claim"));
        }
    }

    /// @dev Pull one principal's refund on `lotId`, asserting the owed amount, the per-pull clone-held
    ///      conservation (held falls by exactly the amount paid), and the event sequence:
    ///      DepositWithdrawn(owed) always; Refunded(escrowLeg) iff `expectRefund` (a winner-escrow
    ///      step-2 exit). vm.expectEmit pins exactly the events declared, so a spurious Refunded on a
    ///      loser pull (cross-pay) diverges. Returns the measured delta.
    function _pullAndMeasure(
        SessionAuction a,
        address payToken,
        address who,
        uint256 lotId,
        uint256 owed,
        bool expectRefund
    ) private returns (uint256 delta) {
        uint256 beforeWho = _bal(a, payToken, who);
        uint256 heldBefore = _held(a, payToken);
        uint256 escrowLeg = uint256(a.getLot(lotId).escrowAmount); // the step-2 Refunded leg, if any

        vm.expectEmit(true, true, false, true, address(a));
        emit ISessionAuction.DepositWithdrawn(lotId, who, owed);
        if (expectRefund) {
            vm.expectEmit(true, true, false, true, address(a));
            emit ISessionAuction.Refunded(lotId, who, escrowLeg);
        }
        vm.prank(who);
        a.withdrawRefund(lotId);

        delta = _bal(a, payToken, who) - beforeWho;
        assertEq(delta, owed, "party delta != owed");

        // Per-pull conservation: held falls by exactly what this party received. Overpaying one party and
        // underpaying another by the same total nets to held==0 overall but fails here.
        assertEq(heldBefore - _held(a, payToken), delta, "clone-held delta != party delta on this pull");
    }

    /// @dev Assert the five-bucket fund-conservation identity on clone `a`:
    ///        held == SUM(free+committed over (lot, principal)) + SUM(escrowAmount) + SUM(disputeBond)
    ///              + SUM(pendingWithdrawal).
    ///      committed is 0 for every principal here (post-hammer/finalize), so the deposit term reduces
    ///      to SUM withdrawableFree. `expectedHeld` is also asserted against the actual held balance, so
    ///      the identity is pinned to a known value, not just an internally-consistent sum.
    function _assertFiveBucket(SessionAuction a, address payToken, uint256 expectedHeld, string memory tag)
        private
        view
    {
        // bucket 1: deposit free (+ committed == 0). Every (lot, principal) that ever funded here.
        uint256 freeSum = a.withdrawableFree(LOT, winner) + a.withdrawableFree(LOT, loser)
            + a.withdrawableFree(LOT2, winner2) + a.withdrawableFree(LOT2, loser2) + a.withdrawableFree(LOT3, winner);
        // buckets 2 + 3: winner escrow + dispute bond, per lot.
        uint256 escrowSum = uint256(a.getLot(LOT).escrowAmount) + uint256(a.getLot(LOT2).escrowAmount)
            + uint256(a.getLot(LOT3).escrowAmount);
        uint256 bondSum = uint256(a.getLot(LOT).disputeBond) + uint256(a.getLot(LOT2).disputeBond)
            + uint256(a.getLot(LOT3).disputeBond);
        // bucket 5: parked withdrawals (0 here; all payees are accepting EOAs).
        uint256 pendingSum = a.pendingWithdrawal(winner) + a.pendingWithdrawal(loser) + a.pendingWithdrawal(winner2)
            + a.pendingWithdrawal(loser2);

        uint256 held = _held(a, payToken);
        assertEq(freeSum + escrowSum + bondSum + pendingSum, held, tag);
        assertEq(held, expectedHeld, tag);
    }

    // Recorded-log assertions (non-emission, which vm.expectEmit cannot prove).

    // Canonical event topic0 hashes (the ABI selector of the event signature). Used to count events
    // in a vm.recordLogs capture so a test can assert the ABSENCE of a spurious event (vm.expectEmit
    // asserts presence only). Signatures are the ISessionAuction declarations verbatim.
    bytes32 private constant DEPOSIT_WITHDRAWN_SIG = keccak256("DepositWithdrawn(uint256,address,uint256)");
    bytes32 private constant REFUNDED_SIG = keccak256("Refunded(uint256,address,uint256)");
    // BidPlaced(uint256 indexed lotId, address indexed principal, uint128 amount, uint64 seq): the
    // promoted bidder's `seq` (non-indexed data) is the voidAndAward candidate.seq the heap matches on.
    bytes32 private constant BID_PLACED_SIG = keccak256("BidPlaced(uint256,address,uint128,uint64)");

    /// @dev Count, over `logs` from the default `auction`, the DepositWithdrawn and Refunded events
    ///      whose indexed (lotId, account) topics match. Lets a test pin exactly-N occurrences (e.g. one
    ///      DepositWithdrawn and zero Refunded on a bond-only pull), which vm.expectEmit cannot.
    function _countWithdrawEvents(Vm.Log[] memory logs, uint256 lotId, address account)
        private
        view
        returns (uint256 depositWithdrawnCount, uint256 refundedCount)
    {
        bytes32 t1 = bytes32(lotId);
        bytes32 t2 = bytes32(uint256(uint160(account)));
        for (uint256 i = 0; i < logs.length; i++) {
            Vm.Log memory lg = logs[i];
            if (lg.emitter != address(auction) || lg.topics.length < 3) continue;
            if (lg.topics[1] != t1 || lg.topics[2] != t2) continue;
            if (lg.topics[0] == DEPOSIT_WITHDRAWN_SIG) depositWithdrawnCount++;
            else if (lg.topics[0] == REFUNDED_SIG) refundedCount++;
        }
    }

    /// @dev Decode the first DepositWithdrawn(lotId, account, amount) from a vm.recordLogs capture on the
    ///      default `auction`. Returns the indexed (lotId, principal) and the non-indexed amount, so a
    ///      test can assert the emitted amount when vm.expectEmit is unusable alongside vm.recordLogs.
    function _firstDepositWithdrawn(Vm.Log[] memory logs, uint256 lotId, address account)
        private
        view
        returns (uint256 emittedLot, address emittedPrincipal, uint256 emittedAmount)
    {
        bytes32 t1 = bytes32(lotId);
        bytes32 t2 = bytes32(uint256(uint160(account)));
        for (uint256 i = 0; i < logs.length; i++) {
            Vm.Log memory lg = logs[i];
            if (lg.emitter != address(auction) || lg.topics.length < 3) continue;
            if (lg.topics[0] != DEPOSIT_WITHDRAWN_SIG) continue;
            if (lg.topics[1] != t1 || lg.topics[2] != t2) continue;
            emittedLot = uint256(lg.topics[1]);
            emittedPrincipal = address(uint160(uint256(lg.topics[2])));
            emittedAmount = abi.decode(lg.data, (uint256));
            return (emittedLot, emittedPrincipal, emittedAmount);
        }
        revert("no matching DepositWithdrawn in recorded logs");
    }

    // Balance / held readers.
    function _bal(SessionAuction, address payToken, address who) private view returns (uint256) {
        return payToken == address(0) ? who.balance : MockERC20(payToken).balanceOf(who);
    }

    function _held(SessionAuction a, address payToken) private view returns (uint256) {
        return payToken == address(0) ? address(a).balance : MockERC20(payToken).balanceOf(address(a));
    }
}

// Adversarial helper contracts (file-level, G_-prefixed to avoid cross-domain symbol collisions).
// None inherit HammerBase.

/// @dev A native receiver that re-enters withdrawRefund on the _pay push to prove the function is
///      nonReentrant. While armed, its receive() re-enters via a low-level call so it can capture the
///      inner revert selector (the OZ guard makes the inner call revert ReentrancyGuardReentrantCall).
///      The capture is load-bearing: the outer _pay is gas-capped with a pull-credit fallback, so a
///      reverting receiver is swallowed and parked rather than bubbled. The test reads `reentered` +
///      `innerSelector` here and asserts the no-double-pay outcome on the clone.
contract G_ReentrantRefund is IERC1271 {
    using ECDSA for bytes32;

    ISessionAuction private immutable auction;
    uint256 private immutable lot;
    address private immutable owner; // the EOA whose key signs this contract's bid envelope (ERC-1271)
    bool private armed;

    bool public reentered; // set true once the re-entrant inner call has been attempted
    bytes4 public innerSelector; // the error selector the inner re-entrant call reverted with

    constructor(ISessionAuction auction_, uint256 lot_, address owner_) {
        auction = auction_;
        lot = lot_;
        owner = owner_;
    }

    /// @dev ERC-1271: accept the bid-ceiling envelope iff the ECDSA signature recovers to the owner.
    ///      SignatureChecker routes a contract principal here.
    function isValidSignature(bytes32 hash, bytes calldata signature) external view override returns (bytes4) {
        address recovered = hash.recover(signature);
        if (recovered != address(0) && recovered == owner) return IERC1271.isValidSignature.selector;
        return 0xffffffff;
    }

    function arm() external {
        armed = true;
    }

    receive() external payable {
        if (armed) {
            armed = false; // one re-entry attempt is enough to trip the guard
            reentered = true;
            // Re-enter via low-level call so the inner revert is captured, not propagated: if this
            // receive() reverted, its `reentered`/`innerSelector` writes would roll back and the test
            // could never read them. The attacker swallows the blocked inner call, records the guard
            // selector, and returns normally; the gas-capped outer push then succeeds (paid once).
            (bool ok, bytes memory ret) =
                address(auction).call(abi.encodeWithSelector(ISessionAuction.withdrawRefund.selector, lot));
            // The re-entrant call must fail (the nonReentrant guard). Capture its selector for the test.
            require(!ok, "reentrancy not blocked");
            if (ret.length >= 4) {
                innerSelector = bytes4(ret);
            }
        }
    }
}

/// @dev A native receiver whose fallback reverts while `reject`, so the gas-capped _pay push fails and
///      withdrawRefund parks the amount to _pendingWithdrawals. Toggle accept so a later claimPending
///      pulls the parked amount (models a temporarily-unable recipient).
contract G_RejectingReceiver is IERC1271 {
    using ECDSA for bytes32;

    address private immutable owner; // the EOA whose key signs this contract's bid envelope (ERC-1271)
    bool public reject = true;

    constructor(address owner_) {
        owner = owner_;
    }

    function setReject(bool v) external {
        reject = v;
    }

    /// @dev ERC-1271: accept the bid-ceiling envelope iff the ECDSA signature recovers to the owner.
    function isValidSignature(bytes32 hash, bytes calldata signature) external view override returns (bytes4) {
        address recovered = hash.recover(signature);
        if (recovered != address(0) && recovered == owner) return IERC1271.isValidSignature.selector;
        return 0xffffffff;
    }

    receive() external payable {
        if (reject) revert("no ether");
    }
}

/// @dev An ERC-20 whose transfer returns false (never reverts) while `fail`, to exercise the
///      SafeERC20.trySafeTransfer -> false -> _pendingWithdrawals credit fallback on the ERC-20 rail.
///      transferFrom always succeeds so deposits/bonds land; only the push leg fails until toggled.
contract G_FalseReturningERC20 is MockERC20 {
    bool public fail = true;

    constructor() MockERC20("G False USD", "gfUSD", 6) {}

    function setFail(bool v) external {
        fail = v;
    }

    function transfer(address to, uint256 value) public override returns (bool) {
        if (fail) return false; // SafeERC20.trySafeTransfer observes false and does NOT revert
        return super.transfer(to, value);
    }
}
