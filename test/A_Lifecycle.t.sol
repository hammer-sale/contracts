// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Lifecycle test suite for SessionAuction: the full Open -> Hammered -> Awaiting -> Delivered ->
// Settled walk plus the NoSale and Voided branches.
//
// Negative tests assert the exact revert selector. State-transition and happy tests drive the real
// entrypoints (initialize, openLot, depositCeiling, placeBid, hammer, finalizeWinner, ...) and
// assert exact phase / deliveryState / packed-Lot fields, emitted events, and exact balances.

import {Initializable} from "@openzeppelin/contracts/proxy/utils/Initializable.sol";
import {Clones}        from "@openzeppelin/contracts/proxy/Clones.sol";

import {HammerBase}      from "./HammerBase.t.sol";
import {SessionAuction}  from "../src/SessionAuction.sol";
import {ISessionAuction} from "../src/interfaces/ISessionAuction.sol";
import {IPaddleRegistry} from "../src/interfaces/IPaddleRegistry.sol";
import {
    Ceiling,
    AttestationQuote,
    NextCleanCandidate,
    InitConfig,
    Lot,
    LotPhase,
    DeliveryState,
    CEILING_TYPEHASH
} from "../src/types/HammerTypes.sol";

contract LifecycleTest is HammerBase {
    // EIP-712 domain typehash, for signing Ceiling envelopes against a clone.
    bytes32 private constant EIP712_DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");

    uint256 private constant LOT_ID = 1;

    // Per-rail reserve base for the happy path. Native uses RESERVE_PRICE (1e18); the 6-decimal
    // ERC-20 rail uses 1e6 (1.000000 mUSD), the same value modulo decimals. A 1e18 base on the ERC-20
    // rail overflows the winner's INITIAL_TOKEN (1e12) balance; 1e6 (and its 2x bid / 3x deposit) fit.
    uint256 private constant TOKEN_RESERVE = 1e6;

    // Key-bearing bidders: HammerBase actors are address-only, but signing a Ceiling needs a key.
    address private winner;
    uint256 private winnerPk;
    address private cleanBidder; // the lower, distinct-paddle bid promoted on a void
    uint256 private cleanBidderPk;

    function setUp() public override {
        super.setUp();
        (winner, winnerPk) = makeAddrAndKey("lifecycleWinner");
        (cleanBidder, cleanBidderPk) = makeAddrAndKey("lifecycleCleanBidder");
        fundEth(winner, INITIAL_ETH);
        fundToken(winner, INITIAL_TOKEN);
        fundEth(cleanBidder, INITIAL_ETH);
        fundToken(cleanBidder, INITIAL_TOKEN);
    }

    /// initialize bounds every config width; one bad field reverts with its named error.
    function test_RevertWhen_InitConfigOutOfRange() public {
        // disputeBondAmt > type(uint96).max -> WrongBond
        SessionAuction a1 = _clone();
        InitConfig memory c1 = _defaultInitConfig(address(0));
        c1.disputeBondAmt = uint128(type(uint96).max) + 1;
        vm.prank(address(hammer));
        vm.expectRevert(ISessionAuction.WrongBond.selector);
        a1.initialize(c1);

        // integrityBondAmt > type(uint96).max -> WrongBond
        SessionAuction a2 = _clone();
        InitConfig memory c2 = _defaultInitConfig(address(0));
        c2.integrityBondAmt = uint128(type(uint96).max) + 1;
        vm.prank(address(hammer));
        vm.expectRevert(ISessionAuction.WrongBond.selector);
        a2.initialize(c2);

        // feeBps > 10_000 -> FeeBpsTooHigh
        SessionAuction a3 = _clone();
        InitConfig memory c3 = _defaultInitConfig(address(0));
        c3.feeBps = 10_001;
        vm.prank(address(hammer));
        vm.expectRevert(ISessionAuction.FeeBpsTooHigh.selector);
        a3.initialize(c3);

        // minIncrementBps > 10_000 -> FeeBpsTooHigh
        SessionAuction a4 = _clone();
        InitConfig memory c4 = _defaultInitConfig(address(0));
        c4.minIncrementBps = 10_001;
        vm.prank(address(hammer));
        vm.expectRevert(ISessionAuction.FeeBpsTooHigh.selector);
        a4.initialize(c4);

        // operatorQx / operatorQy length mismatch -> NoOperatorKeys
        SessionAuction a5 = _clone();
        InitConfig memory c5 = _defaultInitConfig(address(0));
        c5.operatorQy = new bytes32[](2); // qx has length 1
        vm.prank(address(hammer));
        vm.expectRevert(ISessionAuction.NoOperatorKeys.selector);
        a5.initialize(c5);

        // zero operator keys -> NoOperatorKeys
        SessionAuction a6 = _clone();
        InitConfig memory c6 = _defaultInitConfig(address(0));
        c6.operatorQx = new bytes32[](0);
        c6.operatorQy = new bytes32[](0);
        vm.prank(address(hammer));
        vm.expectRevert(ISessionAuction.NoOperatorKeys.selector);
        a6.initialize(c6);
    }

    /// A second initialize on an already-initialized clone reverts InvalidInitialization.
    function test_RevertWhen_InitializeCalledTwice() public {
        SessionAuction a = _clone();
        InitConfig memory cfg = _defaultInitConfig(address(0));

        vm.prank(address(hammer));
        a.initialize(cfg);

        // The (otherwise valid) second init hits the OpenZeppelin initializer guard, not config
        // validation.
        vm.prank(address(hammer));
        vm.expectRevert(Initializable.InvalidInitialization.selector);
        a.initialize(cfg);

        // init seeds the operator set from the on-curve (qx, qy) pair in _defaultInitConfig.
        bytes32 keyId = _baseOperatorKeyId();
        assertTrue(a.isOperatorActive(keyId), "operator key seeded active on init");
    }

    /// The constructor _disableInitializers locks the implementation; the impl cannot init.
    function test_RevertWhen_InitializeImplementation() public {
        // `impl` was deployed directly in HammerBase.setUp(), so its constructor ran
        // _disableInitializers() and initialize on the implementation itself reverts.
        InitConfig memory cfg = _defaultInitConfig(address(0));
        vm.prank(address(hammer));
        vm.expectRevert(Initializable.InvalidInitialization.selector);
        impl.initialize(cfg);
    }

    /// openLot is onlyHammer; a non-hammer caller reverts Unauthorized.
    function test_RevertWhen_OpenLotNotHammer() public {
        SessionAuction a = _initSession(address(0));

        vm.prank(seller); // not the hammer factory role
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        a.openLot(LOT_ID, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));
    }

    /// openLot opens a fresh lot (phase Open; seller / reservePrice / endsAt stored).
    function test_OpenLot() public {
        SessionAuction a = _initSession(address(0));
        uint64 endsAt = uint64(block.timestamp + 1 days);

        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt);

        Lot memory lot = a.getLot(LOT_ID);
        assertEq(uint256(lot.phase), uint256(LotPhase.Open), "phase Open");
        assertEq(lot.seller, seller, "seller stored");
        assertEq(uint256(lot.reservePrice), uint256(RESERVE_PRICE), "reservePrice stored");
        assertEq(uint256(lot.endsAt), uint256(endsAt), "endsAt stored");
        assertEq(uint256(lot.deliveryState), uint256(DeliveryState.None), "no delivery yet");
        assertEq(lot.highBidder, address(0), "no bidder yet");
        assertEq(uint256(lot.highBid), 0, "no bid yet");

        // Clean slate: a freshly-opened lot leaks no stale packed-Lot field (no post-hammer or
        // delivery field carried over from a reused slot).
        assertEq(uint256(lot.winnerSeq), 0, "no winning seq yet");
        assertEq(uint256(lot.hammeredAt), 0, "no hammer anchor yet");
        assertEq(uint256(lot.voidedAt), 0, "no void anchor yet");
        assertEq(uint256(lot.awaitingAt), 0, "no awaiting anchor yet");
        assertEq(uint256(lot.deliveredAt), 0, "no delivered anchor yet");
        assertEq(uint256(lot.escrowAmount), 0, "no escrow yet");
        assertFalse(lot.revealed, "not revealed yet");
        assertEq(uint256(lot.bidIntegrityOpen), 0, "no open integrity dispute");
        assertEq(uint256(lot.paddleId), 0, "no top paddle yet");
        assertEq(uint256(lot.sealedExtensions), 0, "no soft-close extensions yet");
        assertEq(lot.bidBookRoot, bytes32(0), "no bid-book root yet");
    }

    /// openLot is one-shot per lot: it provisions only a phase-None lot and reverts NotOpen on any
    /// live one. Re-opening a live lot would be a fund-safety hole: on an Open lot it resets the hot
    /// slot and orphans committed escrow; on a Hammered or Awaiting lot it orphans the winner's
    /// snapshotted escrowAmount with no exit and resets hammeredAt / awaitingAt / winnerSeq. There is
    /// no dedicated "already provisioned" error, so openLot reuses NotOpen (the lot is not None).
    function test_RevertWhen_OpenLotAlreadyProvisioned() public {
        SessionAuction a = _initSession(address(0));

        // Re-provision parameters all differ from the live lot, so a buggy re-key would visibly
        // clobber seller / reservePrice / endsAt and the assertions below catch it.
        address otherSeller = bidder1;
        uint96 otherReserve = uint96(RESERVE_PRICE) * 7;

        // Leg 1: re-open an OPEN lot.
        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt);

        // A standing bid so the hot slot carries live state a re-key would orphan.
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;
        _deposit(a, address(0), winner, uint256(bidAmount));
        bytes32 ceilingCommit = keccak256(abi.encode(bidAmount, keccak256("reprovision-open-salt")));
        Ceiling memory c = _ceiling(winner, ceilingCommit);
        bytes memory sig = _signCeiling(a, winnerPk, c);
        AttestationQuote memory q = _quote(c, bidAmount, 0, uint128(0), keccak256("qn-reprovision-open"));
        _mockPaddle(winner, _paddleFor(winner)); // placeBid's KYC gate needs a nonzero paddle
        vm.prank(winner);
        a.placeBid(c, LOT_ID, winner, 0, bidAmount, sig, _operatorKeyId(), q);

        Lot memory openLive = a.getLot(LOT_ID);
        assertEq(uint256(openLive.phase), uint256(LotPhase.Open), "leg 1: lot is live in Open with a standing bid");
        assertEq(openLive.highBidder, winner, "leg 1: hot slot carries the standing top bidder");

        // a second openLot on the OPEN lot must revert (lot is not in the provisionable None state).
        vm.prank(address(hammer));
        vm.expectRevert(ISessionAuction.NotOpen.selector);
        a.openLot(LOT_ID, otherSeller, otherReserve, endsAt + 5 days);

        // the live Open lot is unchanged: no re-key of the hot slot or endsAt, no orphan.
        Lot memory openAfter = a.getLot(LOT_ID);
        assertEq(uint256(openAfter.phase), uint256(LotPhase.Open), "leg 1: phase stays Open after blocked re-open");
        assertEq(openAfter.highBidder, winner, "leg 1: hot-slot highBidder unchanged (not orphaned)");
        assertEq(uint256(openAfter.highBid), uint256(bidAmount), "leg 1: hot-slot highBid unchanged");
        assertEq(uint256(openAfter.winnerSeq), uint256(openLive.winnerSeq), "leg 1: winnerSeq unchanged");
        assertEq(openAfter.seller, seller, "leg 1: seller NOT overwritten by the blocked re-open");
        assertEq(uint256(openAfter.reservePrice), uint256(RESERVE_PRICE), "leg 1: reservePrice NOT overwritten");
        assertEq(uint256(openAfter.endsAt), uint256(endsAt), "leg 1: endsAt NOT reset by the blocked re-open");
        // the committed bid is still locked behind the standing top (free stays 0, not orphaned/credited).
        assertEq(a.withdrawableFree(LOT_ID, winner), 0, "leg 1: committed escrow still locked (not orphaned)");

        // Leg 2: re-open a HAMMERED lot with escrowAmount set. A fresh lot driven to Hammered with a
        // real bid, so escrowAmount is the winner's snapshot.
        SessionAuction b = _initSession(address(0));
        _hammerWithBid(b, address(0), bidAmount);

        Lot memory hammered = b.getLot(LOT_ID);
        assertEq(uint256(hammered.phase), uint256(LotPhase.Hammered), "leg 2: lot is Hammered");
        assertEq(uint256(hammered.escrowAmount), uint256(bidAmount), "leg 2: escrowAmount is the winner snapshot");
        assertTrue(hammered.escrowAmount != 0, "leg 2: escrow is live");

        // a second openLot on the HAMMERED lot must revert; otherwise escrowAmount is orphaned.
        vm.prank(address(hammer));
        vm.expectRevert(ISessionAuction.NotOpen.selector);
        b.openLot(LOT_ID, otherSeller, otherReserve, uint64(block.timestamp + 9 days));

        // escrowAmount and the hot slot are unchanged: the snapshotted funds are not orphaned.
        Lot memory hammeredAfter = b.getLot(LOT_ID);
        assertEq(uint256(hammeredAfter.escrowAmount), uint256(bidAmount), "leg 2: escrowAmount NOT orphaned by the blocked re-open");
        assertEq(hammeredAfter.highBidder, winner, "leg 2: winner (hot slot) unchanged");
        assertEq(uint256(hammeredAfter.phase), uint256(LotPhase.Hammered), "leg 2: phase stays Hammered");
        assertEq(uint256(hammeredAfter.hammeredAt), uint256(hammered.hammeredAt), "leg 2: hammeredAt (challenge-window anchor) NOT reset");
        assertEq(uint256(hammeredAfter.winnerSeq), uint256(hammered.winnerSeq), "leg 2: winnerSeq NOT reset");
        assertEq(hammeredAfter.seller, seller, "leg 2: seller NOT overwritten");
        assertEq(uint256(hammeredAfter.endsAt), uint256(hammered.endsAt), "leg 2: endsAt NOT reset");

        // Leg 3: re-open an AWAITING lot (winner final, escrow carried). Finalize the leg-2 lot into
        // Awaiting; _hammerWithBid never revealed, so the reveal gate opens via its past-deadline
        // branch. A re-open here would orphan the carried escrow and reset awaitingAt.
        vm.warp(uint256(hammered.hammeredAt) + AC_CHALLENGE_SEC + REVEAL_DEADLINE_SEC + 1);
        b.finalizeWinner(LOT_ID);

        Lot memory awaiting = b.getLot(LOT_ID);
        assertEq(uint256(awaiting.phase), uint256(LotPhase.Awaiting), "leg 3: lot finalized into Awaiting");
        assertEq(uint256(awaiting.escrowAmount), uint256(bidAmount), "leg 3: finalized escrow carried into Awaiting");

        vm.prank(address(hammer));
        vm.expectRevert(ISessionAuction.NotOpen.selector);
        b.openLot(LOT_ID, otherSeller, otherReserve, uint64(block.timestamp + 9 days));

        Lot memory awaitingAfter = b.getLot(LOT_ID);
        assertEq(uint256(awaitingAfter.phase), uint256(LotPhase.Awaiting), "leg 3: phase stays Awaiting after blocked re-open");
        assertEq(uint256(awaitingAfter.escrowAmount), uint256(bidAmount), "leg 3: carried escrow NOT orphaned by the blocked re-open");
        assertEq(uint256(awaitingAfter.deliveryState), uint256(DeliveryState.AwaitingDelivery), "leg 3: deliveryState NOT reset");
        assertEq(uint256(awaitingAfter.awaitingAt), uint256(awaiting.awaitingAt), "leg 3: awaitingAt (deliver anchor) NOT reset");
        assertEq(awaitingAfter.highBidder, winner, "leg 3: final winner unchanged");
        assertEq(uint256(awaitingAfter.winnerSeq), uint256(awaiting.winnerSeq), "leg 3: winnerSeq NOT reset on the final winner");
    }

    /// hammer Open->Hammered when reserve met; snapshots escrow, emits Hammered.
    function test_HammerReserveMet() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;
        _openDepositBid(a, address(0), bidAmount);

        // Warp past endsAt so the window is closed.
        Lot memory pre = a.getLot(LOT_ID);
        vm.warp(uint256(pre.endsAt) + 1);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Hammered(LOT_ID, winner, bidAmount);
        a.hammer(LOT_ID);

        Lot memory lot = a.getLot(LOT_ID);
        assertEq(uint256(lot.phase), uint256(LotPhase.Hammered), "phase Hammered");
        assertEq(uint256(lot.hammeredAt), block.timestamp, "hammeredAt frozen at now");
        assertEq(uint256(lot.escrowAmount), uint256(bidAmount), "escrowAmount == winner committed");
        assertEq(lot.highBidder, winner, "winner is the high bidder");
        assertEq(uint256(lot.winnerSeq), 1, "winnerSeq set by placeBid, unchanged by hammer");

        // Deposit was exactly the bid (no slack); hammer moved committed -> escrowAmount, leaving
        // nothing free.
        assertEq(a.withdrawableFree(LOT_ID, winner), 0, "winner committed snapshotted away, free == 0");
    }

    /// hammer's _lockEscrow moves the winner's `committed` into lot.escrowAmount and leaves `free`
    /// untouched. With a deposit of bid + nonzero slack, at the hammer boundary: (a) withdrawableFree
    /// == slack exactly, and (b) escrowAmount == bidAmount. Crediting committed back to free instead
    /// of zeroing it would show free == slack + bidAmount.
    function test_HammerSnapshotsCommittedLeavesSlackFree() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;
        uint128 slack = uint128(RESERVE_PRICE); // strictly positive slack, distinct from the bid
        uint256 depositAmount = uint256(bidAmount) + uint256(slack);

        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt);

        // Deposit bidAmount + slack, then bid EXACTLY bidAmount: committed == bidAmount, free == slack.
        _deposit(a, address(0), winner, depositAmount);

        bytes32 ceilingCommit = keccak256(abi.encode(bidAmount, keccak256("slack-hammer-salt")));
        Ceiling memory c = _ceiling(winner, ceilingCommit);
        bytes memory sig = _signCeiling(a, winnerPk, c);
        AttestationQuote memory q = _quote(c, bidAmount, 0, uint128(0), keccak256("qn-slack-hammer"));
        _mockPaddle(winner, _paddleFor(winner)); // placeBid's KYC gate needs a nonzero paddle

        vm.prank(winner);
        a.placeBid(c, LOT_ID, winner, 0, bidAmount, sig, _operatorKeyId(), q);

        // Pre-hammer: the bid is committed, the slack is free.
        assertEq(a.withdrawableFree(LOT_ID, winner), uint256(slack), "pre-hammer: only the slack is free, the bid is committed");

        vm.warp(uint256(endsAt) + 1);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Hammered(LOT_ID, winner, bidAmount);
        a.hammer(LOT_ID);

        // (b) committed moved whole into the escrow snapshot.
        Lot memory lot = a.getLot(LOT_ID);
        assertEq(uint256(lot.phase), uint256(LotPhase.Hammered), "phase Hammered");
        assertEq(uint256(lot.escrowAmount), uint256(bidAmount), "escrowAmount == the committed bid (moved whole)");

        // (a) free stays exactly slack: committed was zeroed, not returned to free.
        assertEq(a.withdrawableFree(LOT_ID, winner), uint256(slack), "winner free == slack EXACTLY at hammer (committed zeroed, not credited back)");
        assertTrue(
            a.withdrawableFree(LOT_ID, winner) != uint256(slack) + uint256(bidAmount),
            "free is NOT slack + bid (committed was not double-counted as withdrawable)"
        );
    }

    /// The hammer window guard is strict `block.timestamp < lot.endsAt`, so the instant
    /// block.timestamp == endsAt is hammerable. Pairs with test_RevertWhen_HammerBeforeEnd, which
    /// asserts the WindowOpen revert at endsAt - 1.
    function test_HammerAtExactEndsAt() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;
        _openDepositBid(a, address(0), bidAmount);

        // Warp to EXACTLY endsAt (not endsAt + 1): block.timestamp == endsAt is NOT < endsAt.
        uint64 endsAt = a.getLot(LOT_ID).endsAt;
        vm.warp(uint256(endsAt));

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Hammered(LOT_ID, winner, bidAmount);
        a.hammer(LOT_ID);

        Lot memory lot = a.getLot(LOT_ID);
        assertEq(uint256(lot.phase), uint256(LotPhase.Hammered), "hammer succeeds at exactly endsAt");
        assertEq(uint256(lot.hammeredAt), uint256(endsAt), "hammeredAt frozen at endsAt");
    }

    /// Reserve boundary: the hammer no-sale guard is
    /// `highBidder == address(0) || uint256(highBid) < reservePrice` (strict `<`), and _minBid returns
    /// reservePrice for the first bid, so `amount >= _minBid` admits exactly reservePrice. At
    /// amount == reservePrice the bid (a) is accepted by placeBid (meets the floor) and (b) hammers to
    /// a SALE, since highBid == reservePrice is not < reservePrice.
    function test_HammerAtExactReserve() public {
        SessionAuction a = _initSession(address(0));
        uint128 exactReserve = uint128(RESERVE_PRICE);

        // (a): a single first bid of exactly reserve is admitted, since _minBid == reserve for the
        // first bid and amount >= _minBid holds at equality.
        _openDepositBid(a, address(0), exactReserve);

        Lot memory pre = a.getLot(LOT_ID);
        assertEq(uint256(pre.highBid), uint256(exactReserve), "exact-reserve bid stands as the top");
        assertEq(pre.highBidder, winner, "exact-reserve bidder is the standing top");

        vm.warp(uint256(pre.endsAt) + 1);

        // (b): highBid == reservePrice is not < reservePrice, so the reserve disjunct is false and the
        // lot hammers to a SALE (Hammered, never NoSale).
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Hammered(LOT_ID, winner, exactReserve);
        a.hammer(LOT_ID);

        Lot memory lot = a.getLot(LOT_ID);
        assertEq(uint256(lot.phase), uint256(LotPhase.Hammered), "exact-reserve hammers to a SALE, not NoSale");
        assertEq(uint256(lot.hammeredAt), block.timestamp, "hammeredAt frozen at the sale");
        assertEq(uint256(lot.escrowAmount), uint256(exactReserve), "escrow snapshot == the exact reserve bid");
        assertEq(lot.highBidder, winner, "winner is the high bidder at exactly reserve");
    }

    /// hammer Open->NoSale when no qualifying bid; distinct terminal, NoSale event, no snapshot.
    function test_HammerNoSale() public {
        SessionAuction a = _initSession(address(0));
        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt);

        // No bids placed; warp past the window.
        vm.warp(uint256(endsAt) + 1);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.NoSale(LOT_ID);
        a.hammer(LOT_ID);

        Lot memory lot = a.getLot(LOT_ID);
        assertEq(uint256(lot.phase), uint256(LotPhase.NoSale), "phase NoSale (terminal)");
        assertEq(uint256(lot.hammeredAt), 0, "no hammeredAt anchor on a no-sale");
        assertEq(uint256(lot.escrowAmount), 0, "no escrow snapshot on a no-sale");

        // No qualifying bid stood, so NoSale leaves no winner imprint.
        assertEq(lot.highBidder, address(0), "no high bidder on a no-sale");
        assertEq(uint256(lot.highBid), 0, "no high bid on a no-sale");
        assertEq(uint256(lot.winnerSeq), 0, "no winnerSeq on a no-sale");
    }

    /// The reserve disjunct of the hammer guard (`highBidder == address(0) || highBid < reservePrice`)
    /// is unreachable through the public bid path, so the hammer-time reserve check is belt-and-
    /// suspenders. placeBid enforces `amount >= _minBid(lot)` and _minBid returns reservePrice with no
    /// standing top, so a sub-reserve first bid reverts BidTooLow and never becomes lot.highBid. With
    /// no top recorded the lot hammers to NoSale via the no-bid disjunct (test_HammerNoSale covers it).
    function test_PlaceBidBlocksSubReserveSoHammerReserveGuardRedundant() public {
        SessionAuction a = _initSession(address(0));
        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt);

        // A strictly-below-reserve first bid. Deposit covers it so the revert is the reserve floor
        // (BidTooLow), not an escrow shortfall (InsufficientFreeBalance).
        uint128 subReserve = uint128(RESERVE_PRICE) - 1;
        _deposit(a, address(0), winner, uint256(subReserve));

        bytes32 ceilingCommit = keccak256(abi.encode(subReserve, keccak256("sub-reserve-salt")));
        Ceiling memory c = _ceiling(winner, ceilingCommit);
        bytes memory sig = _signCeiling(a, winnerPk, c);
        AttestationQuote memory q = _quote(c, subReserve, 0, uint128(0), keccak256("qn-sub-reserve"));

        // placeBid checks the KYC gate before the BidTooLow floor: mock the winner's nonzero paddle so
        // the revert isolates the reserve floor (BidTooLow), not the KYC gate (Unauthorized).
        _mockPaddle(winner, _paddleFor(winner));

        // The public bid path is the only door to lot.highBid and it refuses any sub-reserve top.
        vm.prank(winner);
        vm.expectRevert(ISessionAuction.BidTooLow.selector);
        a.placeBid(c, LOT_ID, winner, 0, subReserve, sig, _operatorKeyId(), q);

        // No top recorded, so the lot is still bid-less; hammer takes the first NoSale disjunct.
        Lot memory pre = a.getLot(LOT_ID);
        assertEq(pre.highBidder, address(0), "sub-reserve bid recorded no top (reserve guard redundant)");
        assertEq(uint256(pre.highBid), 0, "no high bid recorded below reserve");

        vm.warp(uint256(endsAt) + 1);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.NoSale(LOT_ID);
        a.hammer(LOT_ID);

        Lot memory lot = a.getLot(LOT_ID);
        assertEq(uint256(lot.phase), uint256(LotPhase.NoSale), "below-reserve lot hammers to NoSale");
        assertEq(uint256(lot.hammeredAt), 0, "no hammeredAt anchor on the below-reserve no-sale");
        assertEq(uint256(lot.escrowAmount), 0, "no escrow snapshot on the below-reserve no-sale");
    }

    /// hammer reverts NotOpen when the lot is not in the Open phase.
    function test_RevertWhen_HammerNotOpen() public {
        SessionAuction a = _initSession(address(0));
        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt);

        // Drive it to NoSale first (a terminal, no-longer-Open phase).
        vm.warp(uint256(endsAt) + 1);
        a.hammer(LOT_ID);

        // A second hammer reverts NotOpen (phase != Open).
        vm.expectRevert(ISessionAuction.NotOpen.selector);
        a.hammer(LOT_ID);
    }

    /// hammer's `phase != Open` guard blocks a re-hammer of a Hammered lot. This matters because the
    /// SALE body runs `_lockEscrow(lotId, highBidder, highBid)`, which is non-idempotent: a second run
    /// reads the already-zeroed winner.committed and sets lot.escrowAmount = 0, stranding the winner
    /// with NoEscrow at _release. A guard blocking only terminal phases would miss this. Also checks
    /// the Awaiting (finalized) sibling reverts NotOpen with escrow intact, since both phases sit
    /// outside the Open allow-set.
    function test_RevertWhen_HammerAlreadyHammered() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;

        // Open -> Hammered with a real winning bid: the SALE body ran _lockEscrow once, so
        // escrowAmount == the bid and winner.committed is now 0 (the state a second _lockEscrow would
        // mis-read).
        _hammerWithBid(a, address(0), bidAmount);

        Lot memory hammered = a.getLot(LOT_ID);
        assertEq(uint256(hammered.phase), uint256(LotPhase.Hammered), "lot is the SALE (Hammered) phase");
        uint128 escrowBefore = hammered.escrowAmount;
        assertEq(uint256(escrowBefore), uint256(bidAmount), "escrow snapshotted once at the first hammer");
        assertTrue(escrowBefore != 0, "escrow is the live snapshot");

        // Second hammer on the SALE lot: `phase != Open` reverts NotOpen before reaching _lockEscrow.
        vm.expectRevert(ISessionAuction.NotOpen.selector);
        a.hammer(LOT_ID);

        // Escrow is still the bid (not re-locked to 0), and phase / hammeredAt / winnerSeq /
        // highBidder are not re-stamped. A zeroed escrowAmount would brick _release with NoEscrow.
        Lot memory afterReHammer = a.getLot(LOT_ID);
        assertEq(uint256(afterReHammer.escrowAmount), uint256(escrowBefore), "escrow NOT re-locked to 0 by the second hammer");
        assertEq(uint256(afterReHammer.escrowAmount), uint256(bidAmount), "escrow still the winner bid after the blocked re-hammer");
        assertEq(uint256(afterReHammer.phase), uint256(LotPhase.Hammered), "phase stays Hammered (re-hammer blocked)");
        assertEq(uint256(afterReHammer.hammeredAt), uint256(hammered.hammeredAt), "hammeredAt NOT re-stamped by the blocked re-hammer");
        assertEq(uint256(afterReHammer.winnerSeq), uint256(hammered.winnerSeq), "winnerSeq unchanged by the blocked re-hammer");
        assertEq(afterReHammer.highBidder, winner, "winner still the high bidder after the blocked re-hammer");

        // Sibling: an Awaiting (finalized) lot is also outside the Open allow-set, so hammering it
        // reverts NotOpen with escrow intact. _hammerWithBid never revealed, so finalize clears the
        // reveal gate via its past-deadline branch.
        vm.warp(uint256(hammered.hammeredAt) + AC_CHALLENGE_SEC + REVEAL_DEADLINE_SEC + 1);
        a.finalizeWinner(LOT_ID);

        Lot memory awaiting = a.getLot(LOT_ID);
        assertEq(uint256(awaiting.phase), uint256(LotPhase.Awaiting), "lot finalized into Awaiting");
        assertEq(uint256(awaiting.escrowAmount), uint256(bidAmount), "escrow carried into Awaiting unchanged");

        vm.expectRevert(ISessionAuction.NotOpen.selector);
        a.hammer(LOT_ID);

        Lot memory afterAwaitingHammer = a.getLot(LOT_ID);
        assertEq(uint256(afterAwaitingHammer.phase), uint256(LotPhase.Awaiting), "phase stays Awaiting (re-hammer blocked post-finalize)");
        assertEq(uint256(afterAwaitingHammer.escrowAmount), uint256(bidAmount), "Awaiting escrow NOT zeroed by a re-hammer attempt");
    }

    /// hammer reverts WindowOpen while block.timestamp < endsAt.
    function test_RevertWhen_HammerBeforeEnd() public {
        SessionAuction a = _initSession(address(0));
        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt);

        // Still before endsAt.
        vm.warp(uint256(endsAt) - 1);
        vm.expectRevert(ISessionAuction.WindowOpen.selector);
        a.hammer(LOT_ID);

        assertEq(uint256(a.getLot(LOT_ID).phase), uint256(LotPhase.Open), "phase stays Open");
    }

    /// NoSale is terminal; finalizeWinner / markDelivered / commitBidBook all revert.
    function test_RevertWhen_DownstreamAfterNoSale() public {
        SessionAuction a = _initSession(address(0));
        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt);

        vm.warp(uint256(endsAt) + 1);
        a.hammer(LOT_ID); // -> NoSale

        // finalizeWinner requires Hammered or Voided.
        vm.expectRevert(ISessionAuction.NotHammered.selector);
        a.finalizeWinner(LOT_ID);

        // markDelivered requires Awaiting (deliveryState gate).
        vm.prank(seller);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        a.markDelivered(LOT_ID, keccak256("proof"), "ipfs://proof");

        // commitBidBook is post-hammer provenance, never reachable on a no-sale lot.
        vm.prank(settler);
        vm.expectRevert(ISessionAuction.NotHammered.selector);
        a.commitBidBook(LOT_ID, keccak256("root"));

        // voidAndAward checks the phase before the challenge-window anchor: a NoSale lot is not
        // Hammered, so the void path reverts NotHammered.
        NextCleanCandidate memory cand = NextCleanCandidate({
            heapIndex: 0,
            bidder: cleanBidder,
            amount: uint128(RESERVE_PRICE),
            paddleId: 0,
            seq: 1,
            flagNonMembership: new bytes32[](0),
            precedingFlagInclusion: new bytes32[][](0)
        });
        vm.prank(ops);
        vm.expectRevert(ISessionAuction.NotHammered.selector);
        a.voidAndAward(LOT_ID, new bytes32[](0), cand);

        // Phase is unchanged by every blocked downstream call: still the NoSale terminal.
        assertEq(uint256(a.getLot(LOT_ID).phase), uint256(LotPhase.NoSale), "NoSale stays terminal after blocked downstream calls");
    }

    /// A NoSale lot is not Open, so placeBid reverts at its phase guard (`phase == Open else
    /// NotOpen`), refusing to re-animate a dead lot.
    function test_RevertWhen_PlaceBidAfterNoSale() public {
        SessionAuction a = _initSession(address(0));
        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt);

        // Fund the bidder while the lot is still Open (depositCeiling itself guards phase == Open),
        // then drive to NoSale. This leaves a genuine free balance so the post-NoSale bid is funded
        // and the only invalid thing is the terminal phase, isolating the NotOpen phase gate.
        uint128 amount = uint128(RESERVE_PRICE) * 2;
        _deposit(a, address(0), winner, uint256(amount));

        vm.warp(uint256(endsAt) + 1);
        a.hammer(LOT_ID); // -> NoSale (no bids)
        assertEq(uint256(a.getLot(LOT_ID).phase), uint256(LotPhase.NoSale), "lot is the NoSale terminal");

        // A funded, fully-formed bid against the terminal lot: everything except the phase is valid
        // (paddle mocked, real ceiling sig, real attestation), so the revert isolates the NotOpen gate.
        bytes32 ceilingCommit = keccak256(abi.encode(amount, keccak256("post-nosale-salt")));
        Ceiling memory c = _ceiling(winner, ceilingCommit);
        bytes memory sig = _signCeiling(a, winnerPk, c);
        AttestationQuote memory q = _quote(c, amount, 0, uint128(0), keccak256("qn-post-nosale"));
        _mockPaddle(winner, _paddleFor(winner));

        vm.prank(winner);
        vm.expectRevert(ISessionAuction.NotOpen.selector);
        a.placeBid(c, LOT_ID, winner, 0, amount, sig, _operatorKeyId(), q);

        assertEq(uint256(a.getLot(LOT_ID).phase), uint256(LotPhase.NoSale), "phase stays NoSale (no bid re-opened it)");
        assertEq(a.getLot(LOT_ID).highBidder, address(0), "no high bidder imprinted on the terminal lot");
    }

    /// The four delivery exits (confirmReceipt, releaseAfterWindow, reclaimUndelivered, openDispute)
    /// are all unreachable on a NoSale lot (deliveryState None, highBidder address(0)). Each entry
    /// checks its caller modifier before the deliveryState precondition: the onlyBuyer entries
    /// (confirmReceipt, reclaimUndelivered) fail first on msg.sender != highBidder (Unauthorized),
    /// while permissionless releaseAfterWindow and buyer|seller openDispute reach the precondition and
    /// revert WrongDeliveryState (None is neither Delivered nor AwaitingDelivery). Closing these
    /// prevents a phantom payout from a lot that never escrowed.
    function test_RevertWhen_D5ExitsAfterNoSale() public {
        SessionAuction a = _initSession(address(0));
        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt);

        vm.warp(uint256(endsAt) + 1);
        a.hammer(LOT_ID); // -> NoSale

        Lot memory nosale = a.getLot(LOT_ID);
        assertEq(uint256(nosale.deliveryState), uint256(DeliveryState.None), "NoSale lot has no delivery state");
        assertEq(nosale.highBidder, address(0), "NoSale lot has no buyer");

        // confirmReceipt is onlyBuyer: highBidder == address(0), so any caller fails the modifier
        // first (Unauthorized), never reaching _release.
        vm.prank(winner);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        a.confirmReceipt(LOT_ID, keccak256("photo"), "ipfs://photo");

        // reclaimUndelivered is also onlyBuyer: same address(0)-buyer reason -> Unauthorized.
        vm.prank(winner);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        a.reclaimUndelivered(LOT_ID);

        // releaseAfterWindow is permissionless, so it reaches the deliveryState precondition and
        // reverts WrongDeliveryState (None != Delivered) regardless of the timer.
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        a.releaseAfterWindow(LOT_ID);

        // openDispute is buyer|seller. Pranked as seller (== lot.seller) the caller check passes, so
        // it reaches the deliveryState precondition and reverts WrongDeliveryState. The bond is the
        // exact configured amount so the failing condition is the delivery state, not a bond fault.
        vm.prank(seller);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        a.openDispute{value: DISPUTE_BOND_AMT}(LOT_ID, keccak256("claim"));

        // Every delivery exit was rejected: the NoSale lot is still terminal with no delivery state.
        assertEq(uint256(a.getLot(LOT_ID).phase), uint256(LotPhase.NoSale), "phase stays NoSale after blocked delivery exits");
        assertEq(uint256(a.getLot(LOT_ID).deliveryState), uint256(DeliveryState.None), "deliveryState stays None after blocked delivery exits");
    }

    /// commitBidBook is post-hammer provenance, so the settler calling it on a still-Open lot reverts
    /// NotHammered and leaves bidBookRoot at bytes32(0).
    function test_RevertWhen_CommitBidBookBeforeHammer() public {
        SessionAuction a = _initSession(address(0));
        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt); // phase Open, never hammered

        // The settler holds the role, but the lot is not yet Hammered.
        vm.prank(settler);
        vm.expectRevert(ISessionAuction.NotHammered.selector);
        a.commitBidBook(LOT_ID, keccak256("premature-root"));

        assertEq(a.getLot(LOT_ID).bidBookRoot, bytes32(0), "no bid-book root committed pre-hammer");
    }

    /// finalizeWinner moves Hammered->Awaiting once the challenge window closes; it sets
    /// AwaitingDelivery and preserves escrow.
    function test_FinalizeWinner() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;
        _hammerWithBid(a, address(0), bidAmount);

        Lot memory hammered = a.getLot(LOT_ID);
        uint128 escrowBefore = hammered.escrowAmount;

        // Past revealDeadline (opens the reveal gate) and past the challenge window close.
        vm.warp(uint256(hammered.hammeredAt) + AC_CHALLENGE_SEC + REVEAL_DEADLINE_SEC + 1);

        // finalizeWinner moves no money: escrow stays held and is paid out only at _release. Snapshot
        // the contract balance, pending credits, and winner free balance to catch an early payout.
        uint256 contractBefore = address(a).balance;
        uint256 winnerFreeBefore = a.withdrawableFree(LOT_ID, winner);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WinnerFinalized(LOT_ID, winner, bidAmount);
        a.finalizeWinner(LOT_ID);

        Lot memory lot = a.getLot(LOT_ID);
        assertEq(uint256(lot.phase), uint256(LotPhase.Awaiting), "phase Awaiting");
        assertEq(uint256(lot.deliveryState), uint256(DeliveryState.AwaitingDelivery), "AwaitingDelivery");
        assertEq(uint256(lot.awaitingAt), block.timestamp, "awaitingAt frozen at now");
        assertEq(uint256(lot.escrowAmount), uint256(escrowBefore), "escrow preserved, not re-locked");
        assertEq(uint256(lot.escrowAmount), uint256(bidAmount), "escrow still the winner bid");

        // Winner identity carries across the Hammered->Awaiting transition. lot.highBidder is the
        // delivery buyer onlyBuyer keys on (confirmReceipt / reclaimUndelivered), and winnerSeq +
        // hammeredAt are reveal/challenge anchors; finalize is a phase advance, not a re-stamp.
        assertEq(lot.highBidder, winner, "winner/buyer identity preserved into Awaiting (onlyBuyer target)");
        assertEq(uint256(lot.winnerSeq), uint256(hammered.winnerSeq), "winnerSeq preserved across finalize");
        assertEq(uint256(lot.hammeredAt), uint256(hammered.hammeredAt), "hammeredAt anchor not re-stamped by finalize");
        assertEq(uint256(lot.paddleId), uint256(hammered.paddleId), "top paddle preserved across finalize");

        // Finalize is a state-only transition: it never touches the conserved escrow pool.
        assertEq(address(a).balance, contractBefore, "contract native balance unchanged across finalize (no payout fired)");
        assertEq(a.pendingWithdrawal(seller), 0, "no early pending credit minted for the seller at finalize");
        assertEq(a.pendingWithdrawal(winner), 0, "no early pending credit minted for the winner at finalize");
        assertEq(a.withdrawableFree(LOT_ID, winner), winnerFreeBefore, "winner free balance unchanged across finalize");
    }

    /// The finalize gate admits only Hammered or Voided. An Awaiting lot is neither, so a re-finalize
    /// reverts NotHammered before re-stamping awaitingAt (the seller-deliver clock reclaimUndelivered
    /// anchors on) or re-firing WinnerFinalized.
    function test_RevertWhen_FinalizeAlreadyFinalized() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;
        _hammerWithBid(a, address(0), bidAmount);

        Lot memory hammered = a.getLot(LOT_ID);

        // Close the challenge window and open the reveal gate (past revealDeadline), then finalize.
        vm.warp(uint256(hammered.hammeredAt) + AC_CHALLENGE_SEC + REVEAL_DEADLINE_SEC + 1);
        a.finalizeWinner(LOT_ID);

        Lot memory awaiting = a.getLot(LOT_ID);
        assertEq(uint256(awaiting.phase), uint256(LotPhase.Awaiting), "lot is finalized into Awaiting (the re-finalize source)");
        uint256 awaitingAtBefore = uint256(awaiting.awaitingAt);
        uint128 escrowBefore = awaiting.escrowAmount;
        assertEq(awaitingAtBefore, block.timestamp, "awaitingAt anchored at the first finalize (the deliver clock)");
        assertEq(uint256(escrowBefore), uint256(bidAmount), "escrow carried into Awaiting (the re-finalize subject)");

        // Warp further so a re-stamp of awaitingAt would be observably different from the first stamp.
        vm.warp(block.timestamp + 12 hours);
        assertGt(block.timestamp, awaitingAtBefore, "now is strictly after the first awaitingAt, so a re-stamp would be visible");

        // Second finalize on the Awaiting lot: not Hammered/Voided -> NotHammered, before re-stamping.
        vm.expectRevert(ISessionAuction.NotHammered.selector);
        a.finalizeWinner(LOT_ID);

        // The finalized lot is intact: phase Awaiting, the seller-deliver clock (awaitingAt) not
        // reset, the carried escrow not touched, the winner (onlyBuyer target) preserved.
        Lot memory afterReFinalize = a.getLot(LOT_ID);
        assertEq(uint256(afterReFinalize.phase), uint256(LotPhase.Awaiting), "phase stays Awaiting (re-finalize blocked)");
        assertEq(uint256(afterReFinalize.awaitingAt), awaitingAtBefore, "awaitingAt NOT re-stamped (seller-deliver clock not reset)");
        assertEq(uint256(afterReFinalize.deliveryState), uint256(DeliveryState.AwaitingDelivery), "deliveryState unchanged by the blocked re-finalize");
        assertEq(uint256(afterReFinalize.escrowAmount), uint256(escrowBefore), "carried escrow NOT touched by the blocked re-finalize");
        assertEq(afterReFinalize.highBidder, winner, "winner/buyer identity intact after the blocked re-finalize");
    }

    /// The challenge-window gate is inclusive, opening at `block.timestamp >= hammeredAt +
    /// acChallengeSec`: revert at acChallengeSec - 1, success at exactly acChallengeSec. Since
    /// AC_CHALLENGE_SEC == REVEAL_DEADLINE_SEC, at the boundary now == revealDeadline and the deadline
    /// disjunct (`>`) is false, so reveal() opens the reveal gate and isolates the window boundary.
    function test_FinalizeAtExactAcBoundaryWithReveal() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;
        uint128 maxBid = uint128(RESERVE_PRICE) * 5;
        bytes32 salt = keccak256("ac-boundary-salt");
        _hammerWithBidCommit(a, address(0), bidAmount, maxBid, salt);

        uint256 hammeredAt = uint256(a.getLot(LOT_ID).hammeredAt);

        // Satisfy the reveal gate up front so only the challenge-window anchor is under test.
        uint64 winnerSeq = a.getLot(LOT_ID).winnerSeq;
        vm.prank(winner);
        a.reveal(LOT_ID, winnerSeq, maxBid, salt);
        assertTrue(a.getLot(LOT_ID).revealed, "reveal flag set, window boundary now isolated");

        // One second inside the window: finalize still reverts AcWindowOpen (reveal already done).
        vm.warp(hammeredAt + AC_CHALLENGE_SEC - 1);
        vm.expectRevert(ISessionAuction.AcWindowOpen.selector);
        a.finalizeWinner(LOT_ID);
        assertEq(uint256(a.getLot(LOT_ID).phase), uint256(LotPhase.Hammered), "still Hammered at acChallengeSec-1");

        // Exact inclusive boundary: now == hammeredAt + acChallengeSec, finalize succeeds.
        vm.warp(hammeredAt + AC_CHALLENGE_SEC);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WinnerFinalized(LOT_ID, winner, bidAmount);
        a.finalizeWinner(LOT_ID);

        Lot memory lot = a.getLot(LOT_ID);
        assertEq(uint256(lot.phase), uint256(LotPhase.Awaiting), "finalize at exactly acChallengeSec");
        assertEq(uint256(lot.deliveryState), uint256(DeliveryState.AwaitingDelivery), "AwaitingDelivery");
        assertEq(uint256(lot.awaitingAt), block.timestamp, "awaitingAt frozen at the AC boundary");
    }

    /// The reveal gate is `(revealed || block.timestamp > revealDeadline)`. Proves the `revealed` flag
    /// alone opens the gate: with the challenge window closed but the lot still before its
    /// revealDeadline, finalize fails until reveal() and succeeds after. Needs AC_CHALLENGE_SEC <
    /// REVEAL_DEADLINE_SEC for such a strict window to exist; the premise is asserted explicitly.
    function test_FinalizeSucceedsAfterRevealBeforeDeadline() public {
        // Premise: an instant must exist with the challenge window closed but the reveal deadline not
        // yet passed. The HammerBase fixtures set AC_CHALLENGE_SEC == REVEAL_DEADLINE_SEC, so no such
        // window exists (at window close now == revealDeadline, and the deadline disjunct needs `>`).
        // A future fixture with a strictly shorter challenge window runs the body below as written.
        if (AC_CHALLENGE_SEC >= REVEAL_DEADLINE_SEC) {
            // Degenerate window: now == revealDeadline at the boundary, so the deadline disjunct is
            // false and reveal() is the only way to finalize (test_FinalizeAtExactAcBoundaryWithReveal
            // exercises this). Re-assert the boundary equality and skip.
            assertEq(
                uint256(AC_CHALLENGE_SEC),
                uint256(REVEAL_DEADLINE_SEC),
                "fixtures make the window-close instant coincide with revealDeadline; reveal() opens the gate (see test_FinalizeAtExactAcBoundaryWithReveal)"
            );
            return;
        }

        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;
        uint128 maxBid = uint128(RESERVE_PRICE) * 5;
        bytes32 salt = keccak256("reveal-before-deadline-salt");
        _hammerWithBidCommit(a, address(0), bidAmount, maxBid, salt);

        uint256 hammeredAt = uint256(a.getLot(LOT_ID).hammeredAt);

        // Challenge window closed but still strictly before revealDeadline (the gate rests on reveal).
        vm.warp(hammeredAt + AC_CHALLENGE_SEC);
        assertLt(block.timestamp, hammeredAt + REVEAL_DEADLINE_SEC, "still before revealDeadline");

        // Un-revealed: finalize is gated (selector per test_RevertWhen_FinalizeBeforeRevealGate).
        vm.expectRevert(ISessionAuction.AcWindowOpen.selector);
        a.finalizeWinner(LOT_ID);

        // The winner opens their own commitment; the `revealed` flag alone satisfies the gate.
        uint64 winnerSeq = a.getLot(LOT_ID).winnerSeq;
        vm.prank(winner);
        a.reveal(LOT_ID, winnerSeq, maxBid, salt);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WinnerFinalized(LOT_ID, winner, bidAmount);
        a.finalizeWinner(LOT_ID);
        assertEq(uint256(a.getLot(LOT_ID).phase), uint256(LotPhase.Awaiting), "reveal flag alone opened the gate");
    }

    /// finalizeWinner reverts AcWindowOpen while block.timestamp < hammeredAt + acChallengeSec.
    function test_RevertWhen_FinalizeInAcWindow() public {
        SessionAuction a = _initSession(address(0));
        _hammerWithBid(a, address(0), uint128(RESERVE_PRICE) * 2);

        Lot memory hammered = a.getLot(LOT_ID);

        // Still inside the anti-collusion challenge window.
        vm.warp(uint256(hammered.hammeredAt) + AC_CHALLENGE_SEC - 1);

        vm.expectRevert(ISessionAuction.AcWindowOpen.selector);
        a.finalizeWinner(LOT_ID);

        assertEq(uint256(a.getLot(LOT_ID).phase), uint256(LotPhase.Hammered), "phase stays Hammered");
    }

    /// finalizeWinner is gated on `challenge window closed AND (revealed || block.timestamp >
    /// revealDeadline) AND !bidIntegrityDisputeOpen`. Exercises the reveal conjunct alone: at the
    /// instant now == hammeredAt + acChallengeSec the window is closed (`>=`) and the integrity counter
    /// is 0, and since AC_CHALLENGE_SEC == REVEAL_DEADLINE_SEC now == revealDeadline, so the deadline
    /// disjunct (strict `>`) is false; with revealed == false only the reveal gate blocks finalize.
    /// finalize has no dedicated reveal-gate error and reuses AcWindowOpen, which this asserts.
    function test_RevertWhen_FinalizeBeforeRevealGate() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;

        // _hammerWithBid commits a placeholder commitment but does not reveal, so lot.revealed stays
        // false and the reveal gate is the subject under test.
        _hammerWithBid(a, address(0), bidAmount);

        Lot memory hammered = a.getLot(LOT_ID);
        assertFalse(hammered.revealed, "winner is unrevealed (reveal gate under test)");
        assertEq(uint256(hammered.bidIntegrityOpen), 0, "integrity counter clean");

        // Exactly hammeredAt + acChallengeSec: challenge window closed (>=), integrity clean, and
        // now == revealDeadline so the deadline disjunct is false.
        uint256 acClose = uint256(hammered.hammeredAt) + AC_CHALLENGE_SEC;
        vm.warp(acClose);
        assertEq(acClose, uint256(hammered.hammeredAt) + REVEAL_DEADLINE_SEC, "window close coincides with revealDeadline, so only the reveal gate blocks finalize");

        // Unrevealed and not past revealDeadline -> finalize reverts.
        vm.expectRevert(ISessionAuction.AcWindowOpen.selector);
        a.finalizeWinner(LOT_ID);

        Lot memory afterFinalize = a.getLot(LOT_ID);
        assertEq(uint256(afterFinalize.phase), uint256(LotPhase.Hammered), "phase stays Hammered (reveal gate held)");
        assertEq(uint256(afterFinalize.awaitingAt), 0, "no awaitingAt anchor set while reveal-gated");
    }

    /// finalizeWinner reverts BidIntegrityDisputeIsOpen while a bid-integrity dispute is open.
    function test_RevertWhen_FinalizeWithIntegrityDisputeOpen() public {
        SessionAuction a = _initSession(address(0));
        uint64 seq = 1; // the winning bid's seq from the single placeBid in _hammerWithBid
        _hammerWithBid(a, address(0), uint128(RESERVE_PRICE) * 2);

        Lot memory hammered = a.getLot(LOT_ID);

        // Open a bonded bid-integrity dispute on the winning seq (bidIntegrityOpen++).
        vm.prank(bidder2);
        a.challengeAttestation{value: INTEGRITY_BOND_AMT}(LOT_ID, seq, hex"deadbeef");

        // Close the challenge window and reveal gate so only the integrity gate can block finalize.
        vm.warp(uint256(hammered.hammeredAt) + AC_CHALLENGE_SEC + REVEAL_DEADLINE_SEC + 1);

        vm.expectRevert(ISessionAuction.BidIntegrityDisputeIsOpen.selector);
        a.finalizeWinner(LOT_ID);

        assertEq(uint256(a.getLot(LOT_ID).phase), uint256(LotPhase.Hammered), "phase stays Hammered");
    }

    /// A lotId never openLot'd sits at LotPhase.None with winnerSeq 0 and an empty bid book.
    ///
    /// (1) finalizeWinner on a None lot is neither Hammered nor Voided, so it reverts NotHammered.
    ///
    /// (2) reveal on a None lot with seq 0 passes the WrongSeq check (0 == lot.winnerSeq), so it
    /// reaches the commitment check. _ceilingCommitOf[lotId][0] == bytes32(0) and a real opening
    /// keccak256(abi.encode(maxBid, salt)) can never be bytes32(0), so reveal reverts
    /// CommitmentMismatch and cannot flip the gate on a lot that never had a bid.
    function test_RevertWhen_FinalizeUnopenedLot() public {
        // A fresh, initialized session with NO openLot: lot 1 is at LotPhase.None.
        SessionAuction a = _initSession(address(0));

        Lot memory none = a.getLot(LOT_ID);
        assertEq(uint256(none.phase), uint256(LotPhase.None), "never-opened lot is phase None");
        assertEq(uint256(none.winnerSeq), 0, "never-opened lot has winnerSeq 0 (the seq==0 reveal edge)");

        // (1) finalizeWinner on a None lot: not Hammered/Voided -> NotHammered.
        vm.expectRevert(ISessionAuction.NotHammered.selector);
        a.finalizeWinner(LOT_ID);

        // (2) reveal(LOT_ID, 0, ...) on a None lot: seq 0 passes the WrongSeq check (0 == winnerSeq),
        // then the empty commitment slot bytes32(0) cannot match the real opening -> CommitmentMismatch.
        vm.prank(winner);
        vm.expectRevert(ISessionAuction.CommitmentMismatch.selector);
        a.reveal(LOT_ID, 0, uint128(RESERVE_PRICE), keccak256("phantom-salt"));

        // Neither blocked entry mutated the phantom lot.
        Lot memory afterCalls = a.getLot(LOT_ID);
        assertEq(uint256(afterCalls.phase), uint256(LotPhase.None), "phase stays None");
        assertFalse(afterCalls.revealed, "reveal did not flip the gate on a never-opened lot");
    }

    /// finalizeWinner must NOT re-snapshot escrow; escrowAmount survives finalize.
    function test_FinalizeDoesNotReLockEscrow() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 3;
        _hammerWithBid(a, address(0), bidAmount);

        Lot memory hammered = a.getLot(LOT_ID);
        assertEq(uint256(hammered.escrowAmount), uint256(bidAmount), "escrow snapshotted once at hammer");

        vm.warp(uint256(hammered.hammeredAt) + AC_CHALLENGE_SEC + REVEAL_DEADLINE_SEC + 1);
        a.finalizeWinner(LOT_ID);

        // A second _lockEscrow would read the zeroed committed and set escrowAmount = 0, then a later
        // _release would brick with NoEscrow. finalize must leave the snapshot intact.
        Lot memory finalized = a.getLot(LOT_ID);
        assertEq(uint256(finalized.escrowAmount), uint256(bidAmount), "escrow unchanged by finalize");
        assertTrue(finalized.escrowAmount != 0, "escrow not zeroed (no NoEscrow strand)");
    }

    /// A Voided lot finalizes Voided->Awaiting into the same AwaitingDelivery node as any winner.
    function test_FinalizeAfterVoid() public {
        SessionAuction a = _initSession(address(0));

        // Two distinct-paddle bids: cleanBidder lower (seq 1), winner higher (seq 2, provisional top).
        uint128 promotedAmount = uint128(RESERVE_PRICE) * 2;
        _hammerWithTwoBids(a, address(0), promotedAmount, uint128(RESERVE_PRICE) * 3);

        Lot memory hammered = a.getLot(LOT_ID);

        // Void the flagged provisional winner inside the challenge window and promote cleanBidder
        // (seq 1). Arm the flag tree before the expectEmit so its FlagRootCommitted does not land in
        // the LotVoided window, then drive the void directly with the built proofs.
        vm.warp(uint256(hammered.hammeredAt) + 1);
        (bytes32[] memory memProof, NextCleanCandidate memory cand) =
            _armVoidFlagTree(a, cleanBidder, promotedAmount, 1);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.LotVoided(LOT_ID, winner, cleanBidder, promotedAmount);
        vm.prank(ops);
        a.voidAndAward(LOT_ID, memProof, cand);

        Lot memory voided = a.getLot(LOT_ID);
        assertEq(uint256(voided.phase), uint256(LotPhase.Voided), "phase Voided after void");
        assertTrue(voided.voidedAt != 0, "voidedAt anchor set");

        // winnerSeq re-bind: _verifyAndPromote sets lot.winnerSeq = candidate.seq so a later reveal /
        // challengeOverCeiling binds to the promoted bid, not the voided offender's. The offender
        // (winner) was seq 2; the promoted cleanBidder is seq 1, so winnerSeq must now be 1.
        assertEq(uint256(voided.winnerSeq), 1, "winnerSeq re-bound to the promoted candidate, off the offender seq 2");

        // The re-bound seq is the one reveal accepts: cleanBidder opens their own seq-1 commitment
        // (keccak256(abi.encode(promotedAmount, keccak256("salt1"))) from _hammerWithTwoBids); it flips
        // lot.revealed only because winnerSeq was re-bound to 1.
        vm.prank(cleanBidder);
        a.reveal(LOT_ID, voided.winnerSeq, promotedAmount, keccak256("salt1"));
        assertTrue(a.getLot(LOT_ID).revealed, "reveal of the re-bound winnerSeq (promoted candidate) flips the gate");

        // Finalize the promoted winner once block.timestamp >= voidedAt + acChallengeSec.
        vm.warp(uint256(voided.voidedAt) + AC_CHALLENGE_SEC + REVEAL_DEADLINE_SEC + 1);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WinnerFinalized(LOT_ID, cleanBidder, promotedAmount);
        a.finalizeWinner(LOT_ID);

        Lot memory lot = a.getLot(LOT_ID);
        assertEq(uint256(lot.phase), uint256(LotPhase.Awaiting), "Voided->Awaiting (same node)");
        assertEq(uint256(lot.deliveryState), uint256(DeliveryState.AwaitingDelivery), "AwaitingDelivery");
        assertEq(uint256(lot.awaitingAt), block.timestamp, "awaitingAt set on promoted finalize");
        assertEq(lot.highBidder, cleanBidder, "promoted winner is the high bidder");

        // Voided->Awaiting escrow carry: the void promoted the lower bid (cleanBidder at 2x reserve)
        // over the offender (winner at 3x), zeroing the offender's escrow and re-locking the promoted
        // bidder's own bid. The carried escrow must be exactly promotedAmount: not the stale offender
        // 3x, and not 0 (0 would brick the promoted winner's _release with NoEscrow).
        assertEq(
            uint256(lot.escrowAmount),
            uint256(promotedAmount),
            "finalized escrow == promoted bidder own bid, not offender 3x, not re-locked to 0"
        );
        assertTrue(lot.escrowAmount != 0, "escrow carried, not re-snapshotted to 0 (no NoEscrow strand on the void-finalize path)");
        assertTrue(lot.escrowAmount != uint128(RESERVE_PRICE) * 3, "carried escrow is the promoted 2x, never the offender 3x");
    }

    /// A Voided lot finalizes only once `block.timestamp >= voidedAt + acChallengeSec`, a second
    /// challenge pass anchored on voidedAt, not hammeredAt. Voids late in the hammer window (the last
    /// legal instant hammeredAt + acChallengeSec - 1) so the original window elapses well before the
    /// void window, proving finalize is gated on the void anchor (a hammeredAt-anchored bug would skip
    /// the second pass).
    function test_RevertWhen_FinalizeVoidedInWindow() public {
        SessionAuction a = _initSession(address(0));
        uint128 promotedAmount = uint128(RESERVE_PRICE) * 2;
        _hammerWithTwoBids(a, address(0), promotedAmount, uint128(RESERVE_PRICE) * 3);

        uint256 hammeredAt = uint256(a.getLot(LOT_ID).hammeredAt);

        // Void at the last legal instant of the hammer window (voidAndAward needs
        // block.timestamp < hammeredAt + acChallengeSec), so voidedAt = hammeredAt + acChallengeSec - 1.
        // The original window then expires a full (acChallengeSec - 1) before the void window, so a
        // hammeredAt-anchored bug would let finalize through at the revert instants below.
        vm.warp(hammeredAt + AC_CHALLENGE_SEC - 1);
        _voidAndAward(a, cleanBidder, promotedAmount, 1);

        uint256 voidedAt = uint256(a.getLot(LOT_ID).voidedAt);
        assertEq(voidedAt, hammeredAt + AC_CHALLENGE_SEC - 1, "voidedAt frozen at the late void");
        assertEq(uint256(a.getLot(LOT_ID).phase), uint256(LotPhase.Voided), "phase Voided");

        // Satisfy the reveal gate up front so only the void-anchored challenge window is under test.
        // For a Voided lot finalizeWinner re-anchors the challenge window and reveal deadline on
        // voidedAt (the promoted winner's window). Since AC_CHALLENGE_SEC == REVEAL_DEADLINE_SEC, at
        // the boundary now == reveal deadline and the deadline disjunct (strict `>`) is false, so
        // reveal() is the only way to open the gate. winnerSeq was re-bound to the promoted seq 1, so
        // cleanBidder opens its own commitment; reveal flips only `revealed`, not the window.
        uint64 promotedSeq = a.getLot(LOT_ID).winnerSeq; // == 1, re-bound to the promoted candidate
        vm.prank(cleanBidder);
        a.reveal(LOT_ID, promotedSeq, promotedAmount, keccak256("salt1"));
        assertTrue(a.getLot(LOT_ID).revealed, "promoted winner revealed, void-anchored window now isolated");

        // Adversarial instant: past the original hammer window but inside the fresh void window.
        // voidedAt + AC_CHALLENGE_SEC - 1 == hammeredAt + 2*acChallengeSec - 2 > hammeredAt +
        // acChallengeSec (the original window close), so the gate cannot be reading hammeredAt. The
        // reveal flag is set, so the only thing still blocking finalize is the void-anchored window.
        uint256 adversarial = voidedAt + AC_CHALLENGE_SEC - 1;
        assertGt(adversarial, hammeredAt + AC_CHALLENGE_SEC, "revert instant is already past the ORIGINAL hammer window");
        vm.warp(adversarial);
        vm.expectRevert(ISessionAuction.AcWindowOpen.selector);
        a.finalizeWinner(LOT_ID);
        assertEq(uint256(a.getLot(LOT_ID).phase), uint256(LotPhase.Voided), "phase stays Voided inside the void window");

        // Exact inclusive boundary on the void anchor: success at voidedAt + acChallengeSec. The
        // challenge window just closed (>=) and `revealed` already opened the reveal gate, so finalize
        // succeeds purely because the void anchor's challenge window elapsed.
        vm.warp(voidedAt + AC_CHALLENGE_SEC);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.WinnerFinalized(LOT_ID, cleanBidder, promotedAmount);
        a.finalizeWinner(LOT_ID);

        Lot memory lot = a.getLot(LOT_ID);
        assertEq(uint256(lot.phase), uint256(LotPhase.Awaiting), "Voided->Awaiting at exactly voidedAt + acChallengeSec");
        assertEq(uint256(lot.deliveryState), uint256(DeliveryState.AwaitingDelivery), "AwaitingDelivery");
        assertEq(lot.highBidder, cleanBidder, "promoted winner finalized on the void anchor");
    }

    /// reveal binds the WINNING bid, opens the commitment, sets lot.revealed.
    function test_Reveal() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;
        uint128 maxBid = uint128(RESERVE_PRICE) * 5;
        bytes32 salt = keccak256("winner-secret-salt");
        _hammerWithBidCommit(a, address(0), bidAmount, maxBid, salt);

        // reveal flips a single packed bit: `revealed` shares its storage slot with hammeredAt,
        // voidedAt, and bidIntegrityOpen. Pin every co-packed neighbor (plus phase / escrowAmount /
        // winnerSeq) to verify reveal is a no-side-effect flag flip that does not clobber the slot.
        Lot memory pre = a.getLot(LOT_ID);
        uint64 winnerSeq = pre.winnerSeq; // == 1
        assertEq(uint256(winnerSeq), 1, "winnerSeq is the single placed bid");
        assertFalse(pre.revealed, "lot starts un-revealed");
        assertTrue(pre.hammeredAt != 0, "hammeredAt set (a packed-slot neighbor under no-clobber watch)");
        assertEq(uint256(pre.bidIntegrityOpen), 0, "integrity counter clean pre-reveal (another packed-slot neighbor)");

        vm.prank(winner); // the recorded principal of the winning bid
        a.reveal(LOT_ID, winnerSeq, maxBid, salt);

        // Everything except `revealed` is unchanged: reveal flips only that bit.
        Lot memory post = a.getLot(LOT_ID);
        assertTrue(post.revealed, "lot.revealed flipped true by the winner opening");
        assertEq(uint256(post.phase), uint256(LotPhase.Hammered), "phase unchanged by reveal (still Hammered)");
        assertEq(uint256(post.escrowAmount), uint256(bidAmount), "escrowAmount untouched by reveal");
        assertEq(uint256(post.winnerSeq), uint256(winnerSeq), "winnerSeq untouched by reveal");
        assertEq(uint256(post.hammeredAt), uint256(pre.hammeredAt), "co-packed hammeredAt intact across reveal");
        assertEq(uint256(post.voidedAt), uint256(pre.voidedAt), "co-packed voidedAt intact across reveal");
        assertEq(uint256(post.bidIntegrityOpen), 0, "co-packed bidIntegrityOpen untouched (still 0) by reveal");
        assertEq(uint256(post.deliveryState), uint256(DeliveryState.None), "deliveryState not advanced by reveal");
        assertEq(post.highBidder, pre.highBidder, "highBidder untouched by reveal");
        assertEq(uint256(post.highBid), uint256(pre.highBid), "highBid untouched by reveal");
    }

    /// reveal has no phase guard and only the WrongSeq / CommitmentMismatch / NotPrincipal checks (no
    /// already-revealed error), so a repeated correct reveal re-passes all three and is a monotonic
    /// no-op. Pins both:
    ///   (1) double reveal while still Hammered: the second leaves the full Lot unchanged (revealed
    ///       stays true; phase / escrowAmount / winnerSeq / packed neighbors intact);
    ///   (2) reveal after finalize (Awaiting): a third reveal on the live delivery lot does not disturb
    ///       the finalized winner (phase, awaitingAt, escrowAmount, highBidder intact).
    function test_RevealIsIdempotent() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;
        uint128 maxBid = uint128(RESERVE_PRICE) * 5;
        bytes32 salt = keccak256("idempotent-reveal-salt");
        _hammerWithBidCommit(a, address(0), bidAmount, maxBid, salt);

        uint64 winnerSeq = a.getLot(LOT_ID).winnerSeq;
        assertEq(uint256(winnerSeq), 1, "winnerSeq is the single placed bid");

        // first reveal: flips the gate (the flag-flip proved in test_Reveal).
        vm.prank(winner);
        a.reveal(LOT_ID, winnerSeq, maxBid, salt);

        Lot memory afterFirst = a.getLot(LOT_ID);
        assertTrue(afterFirst.revealed, "first reveal flips the gate true");
        assertEq(uint256(afterFirst.phase), uint256(LotPhase.Hammered), "still Hammered after the first reveal");

        // (1) second reveal while still Hammered, same correct (seq, maxBid, salt) from the same
        // principal: re-passes all three checks and must be a monotonic no-op (revealed stays true,
        // every other field unchanged from afterFirst).
        vm.prank(winner);
        a.reveal(LOT_ID, winnerSeq, maxBid, salt);

        Lot memory afterSecond = a.getLot(LOT_ID);
        assertTrue(afterSecond.revealed, "double reveal stays revealed (monotonic, not toggled off)");
        assertEq(uint256(afterSecond.phase), uint256(LotPhase.Hammered), "phase unchanged by the repeated reveal (still Hammered)");
        assertEq(uint256(afterSecond.escrowAmount), uint256(afterFirst.escrowAmount), "escrowAmount untouched by the repeated reveal");
        assertEq(uint256(afterSecond.escrowAmount), uint256(bidAmount), "escrowAmount still the winner bid after the repeated reveal");
        assertEq(uint256(afterSecond.winnerSeq), uint256(winnerSeq), "winnerSeq untouched by the repeated reveal");
        assertEq(uint256(afterSecond.hammeredAt), uint256(afterFirst.hammeredAt), "co-packed slot-1 hammeredAt intact across the repeated reveal");
        assertEq(uint256(afterSecond.voidedAt), uint256(afterFirst.voidedAt), "co-packed slot-1 voidedAt intact across the repeated reveal");
        assertEq(uint256(afterSecond.bidIntegrityOpen), uint256(afterFirst.bidIntegrityOpen), "co-packed slot-1 bidIntegrityOpen untouched by the repeated reveal");
        assertEq(uint256(afterSecond.deliveryState), uint256(DeliveryState.None), "deliveryState not advanced by the repeated reveal");
        assertEq(afterSecond.highBidder, afterFirst.highBidder, "highBidder untouched by the repeated reveal");
        assertEq(uint256(afterSecond.highBid), uint256(afterFirst.highBid), "highBid untouched by the repeated reveal");

        // (2) reveal after finalize: drive the lot to Awaiting, then reveal a third time with the same
        // opening on the live delivery lot. With no phase guard it must remain a no-op.
        vm.warp(uint256(afterSecond.hammeredAt) + AC_CHALLENGE_SEC + REVEAL_DEADLINE_SEC + 1);
        a.finalizeWinner(LOT_ID);

        Lot memory awaiting = a.getLot(LOT_ID);
        assertEq(uint256(awaiting.phase), uint256(LotPhase.Awaiting), "lot finalized into Awaiting (reveal flag opened the gate)");

        vm.prank(winner);
        a.reveal(LOT_ID, winnerSeq, maxBid, salt);

        Lot memory afterPostFinalizeReveal = a.getLot(LOT_ID);
        assertTrue(afterPostFinalizeReveal.revealed, "reveal stays true post-finalize (still monotonic)");
        assertEq(uint256(afterPostFinalizeReveal.phase), uint256(LotPhase.Awaiting), "post-finalize reveal does NOT regress or advance the phase (stays Awaiting)");
        assertEq(uint256(afterPostFinalizeReveal.deliveryState), uint256(DeliveryState.AwaitingDelivery), "post-finalize reveal does NOT disturb the live D5 deliveryState");
        assertEq(uint256(afterPostFinalizeReveal.awaitingAt), uint256(awaiting.awaitingAt), "post-finalize reveal does NOT re-stamp the seller-deliver anchor");
        assertEq(uint256(afterPostFinalizeReveal.escrowAmount), uint256(bidAmount), "post-finalize reveal does NOT touch the carried escrow");
        assertEq(afterPostFinalizeReveal.highBidder, winner, "post-finalize reveal does NOT clobber the onlyBuyer target");
    }

    /// reveal with seq != lot.winnerSeq reverts WrongSeq.
    function test_RevertWhen_RevealWrongSeq() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;
        uint128 maxBid = uint128(RESERVE_PRICE) * 5;
        bytes32 salt = keccak256("winner-secret-salt");
        _hammerWithBidCommit(a, address(0), bidAmount, maxBid, salt);

        uint64 winnerSeq = a.getLot(LOT_ID).winnerSeq;
        uint64 wrongSeq = winnerSeq + 1; // not the winning seq

        vm.prank(winner);
        vm.expectRevert(ISessionAuction.WrongSeq.selector);
        a.reveal(LOT_ID, wrongSeq, maxBid, salt);
    }

    /// reveal binds strictly to lot.winnerSeq even when the supplied seq is a valid placed bid with
    /// stored _bidOf / _ceilingCommitOf data (test_RevertWhen_RevealWrongSeq only uses a non-existent
    /// seq). cleanBidder is the losing seq-1 bid, winner the top at seq 2. The loser opens their own
    /// seq-1 commitment correctly, yet it reverts WrongSeq because seq 1 != lot.winnerSeq, proving
    /// reveal binds to the winner, not merely an openable commitment.
    function test_RevertWhen_RevealWrongButExistingSeq() public {
        SessionAuction a = _initSession(address(0));

        // cleanBidder bids lowAmount (seq 1, losing); winner bids highAmount (seq 2, top).
        uint128 lowAmount = uint128(RESERVE_PRICE) * 2;
        uint128 highAmount = uint128(RESERVE_PRICE) * 3;
        _hammerWithTwoBids(a, address(0), lowAmount, highAmount);

        // the running top is the winner's seq 2; the loser's bid is a real, stored, openable seq 1.
        assertEq(uint256(a.getLot(LOT_ID).winnerSeq), 2, "winnerSeq is the top bid (seq 2)");

        // cleanBidder opens their own seq-1 commitment correctly (keccak256(abi.encode(lowAmount,
        // keccak256("salt1"))) from _hammerWithTwoBids, and cleanBidder is the seq-1 principal). The
        // only defect is seq 1 != lot.winnerSeq, so the bind-to-winner gate fires first.
        uint64 losingSeq = 1;
        vm.prank(cleanBidder);
        vm.expectRevert(ISessionAuction.WrongSeq.selector);
        a.reveal(LOT_ID, losingSeq, lowAmount, keccak256("salt1"));

        // the gate held: no spurious revealed flag from opening a non-winning bid.
        assertFalse(a.getLot(LOT_ID).revealed, "revealing a losing (non-winner) seq does not flip the gate");
    }

    /// reveal from a caller who is not the recorded principal reverts NotPrincipal.
    function test_RevertWhen_RevealNotPrincipal() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;
        uint128 maxBid = uint128(RESERVE_PRICE) * 5;
        bytes32 salt = keccak256("winner-secret-salt");
        _hammerWithBidCommit(a, address(0), bidAmount, maxBid, salt);

        uint64 winnerSeq = a.getLot(LOT_ID).winnerSeq;

        vm.prank(bidder3); // not the winning bid's principal
        vm.expectRevert(ISessionAuction.NotPrincipal.selector);
        a.reveal(LOT_ID, winnerSeq, maxBid, salt);
    }

    /// reveal with a bad opening (wrong maxBid/salt) reverts CommitmentMismatch.
    function test_RevertWhen_RevealCommitmentMismatch() public {
        SessionAuction a = _initSession(address(0));
        uint128 bidAmount = uint128(RESERVE_PRICE) * 2;
        uint128 maxBid = uint128(RESERVE_PRICE) * 5;
        bytes32 salt = keccak256("winner-secret-salt");
        _hammerWithBidCommit(a, address(0), bidAmount, maxBid, salt);

        uint64 winnerSeq = a.getLot(LOT_ID).winnerSeq;

        // correct seq + principal, but the opening does not match the stored ceilingCommit.
        vm.prank(winner);
        vm.expectRevert(ISessionAuction.CommitmentMismatch.selector);
        a.reveal(LOT_ID, winnerSeq, maxBid + 1, salt);
    }

    /// commitBidBook is onlySettler; a non-settler caller reverts Unauthorized.
    function test_RevertWhen_CommitBidBookNotSettler() public {
        SessionAuction a = _initSession(address(0));
        _hammerWithBid(a, address(0), uint128(RESERVE_PRICE) * 2);

        vm.prank(bidder1); // not the settler role
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        a.commitBidBook(LOT_ID, keccak256("bid-book-root"));
    }

    /// settler commits the post-hammer bid-book root and emits BidBookCommitted.
    function test_CommitBidBook() public {
        SessionAuction a = _initSession(address(0));
        _hammerWithBid(a, address(0), uint128(RESERVE_PRICE) * 2);

        bytes32 root = keccak256("bid-book-root");

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.BidBookCommitted(LOT_ID, root);
        vm.prank(settler);
        a.commitBidBook(LOT_ID, root);

        assertEq(a.getLot(LOT_ID).bidBookRoot, root, "bidBookRoot stored");
    }

    /// Full end-to-end happy path on both rails (native and 6-decimal ERC-20).
    function test_FullLifecycleHappyPath() public {
        _fullLifecycle(address(0));    // native rail
        _fullLifecycle(address(token)); // ERC-20 rail (identical accounting modulo decimals)
    }

    // Private helpers (this contract only).

    /// @dev A fresh, uninitialized SessionAuction clone of the locked implementation.
    function _clone() private returns (SessionAuction) {
        return SessionAuction(Clones.clone(address(impl)));
    }

    /// @dev A fresh clone initialized for `paymentToken` by the hammer factory role. HammerBase.setUp
    ///      registers only the singleton `auction` clone on the Treasury / AgentBond pools, so a fresh
    ///      clone is not in either onlyAuction set and the void-path depositForfeit would revert
    ///      Unauthorized. The test contract owns both pools, so it registers the clone directly.
    function _initSession(address paymentToken) private returns (SessionAuction a) {
        a = _clone();
        InitConfig memory cfg = _defaultInitConfig(paymentToken);
        vm.prank(address(hammer));
        a.initialize(cfg);
        treasury.registerClone(address(a));     // forfeit-route (depositForfeit) onlyAuction gate
        operatorBond.registerClone(address(a));  // bond-pool onlyAuction gate (parity with the base wiring)
    }

    /// @dev openLot + deposit `amount` for `winner` + a single signed placeBid of `amount`.
    ///      Uses ceilingCommit over (amount, salt) with `amount` doubling as a placeholder maxBid.
    function _openDepositBid(SessionAuction a, address paymentToken, uint128 amount) private {
        _openDepositBidCommit(a, paymentToken, amount, amount, keccak256("default-salt"), winner, winnerPk, 0);
    }

    /// @dev As above but with an explicit committed maxBid + salt (for reveal tests).
    function _openDepositBidCommit(
        SessionAuction a,
        address paymentToken,
        uint128 amount,
        uint128 maxBid,
        bytes32 salt,
        address principal,
        uint256 pk,
        uint64 bidIndex
    ) private {
        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt);

        _deposit(a, paymentToken, principal, uint256(amount));

        bytes32 ceilingCommit = keccak256(abi.encode(maxBid, salt));
        Ceiling memory c = _ceiling(principal, ceilingCommit);
        bytes memory sig = _signCeiling(a, pk, c);
        AttestationQuote memory q = _quote(c, amount, bidIndex, uint128(0), keccak256("qn-opendeposit"));

        // placeBid's KYC gate: mock a distinct nonzero paddle for the bidder, else the bid reverts
        // Unauthorized() before reaching the bid logic.
        _mockPaddle(principal, _paddleFor(principal));

        vm.prank(principal);
        a.placeBid(c, LOT_ID, principal, bidIndex, amount, sig, _operatorKeyId(), q);
    }

    /// @dev Drive a lot to Hammered with a single winning bid of `amount`.
    function _hammerWithBid(SessionAuction a, address paymentToken, uint128 amount) private {
        _openDepositBid(a, paymentToken, amount);

        Lot memory pre = a.getLot(LOT_ID);
        vm.warp(uint256(pre.endsAt) + 1);
        a.hammer(LOT_ID);
    }

    /// @dev Hammered with a single winning bid whose commitment opens to (maxBid, salt).
    function _hammerWithBidCommit(
        SessionAuction a,
        address paymentToken,
        uint128 amount,
        uint128 maxBid,
        bytes32 salt
    ) private {
        _openDepositBidCommit(a, paymentToken, amount, maxBid, salt, winner, winnerPk, 0);

        Lot memory pre = a.getLot(LOT_ID);
        vm.warp(uint256(pre.endsAt) + 1);
        a.hammer(LOT_ID);
    }

    /// @dev Hammered with two distinct-paddle bids: cleanBidder at `lowAmount` (seq 1), winner at
    ///      `highAmount` (seq 2, provisional top). Used by the void-then-finalize path.
    function _hammerWithTwoBids(
        SessionAuction a,
        address paymentToken,
        uint128 lowAmount,
        uint128 highAmount
    ) private {
        uint64 endsAt = uint64(block.timestamp + 1 days);
        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, RESERVE_PRICE, endsAt);

        // cleanBidder deposits + places the lower (clean) bid first -> seq 1. Each principal gets a
        // distinct nonzero KYC paddle so the gate passes and the hot-slot paddleId tracks them.
        _deposit(a, paymentToken, cleanBidder, uint256(lowAmount));
        bytes32 commit1 = keccak256(abi.encode(lowAmount, keccak256("salt1")));
        Ceiling memory c1 = _ceiling(cleanBidder, commit1);
        bytes memory sig1 = _signCeiling(a, cleanBidderPk, c1);
        AttestationQuote memory q1 = _quote(c1, lowAmount, 0, uint128(0), keccak256("qn-two-bids-1"));
        _mockPaddle(cleanBidder, _paddleFor(cleanBidder));
        vm.prank(cleanBidder);
        a.placeBid(c1, LOT_ID, cleanBidder, 0, lowAmount, sig1, _operatorKeyId(), q1);

        // winner deposits + places the higher bid -> seq 2 (becomes provisional top).
        _deposit(a, paymentToken, winner, uint256(highAmount));
        bytes32 commit2 = keccak256(abi.encode(highAmount, keccak256("salt2")));
        Ceiling memory c2 = _ceiling(winner, commit2);
        bytes memory sig2 = _signCeiling(a, winnerPk, c2);
        AttestationQuote memory q2 = _quote(c2, highAmount, 0, uint128(lowAmount), keccak256("qn-two-bids-2"));
        _mockPaddle(winner, _paddleFor(winner));
        vm.prank(winner);
        a.placeBid(c2, LOT_ID, winner, 0, highAmount, sig2, _operatorKeyId(), q2);

        vm.warp(uint256(endsAt) + 1);
        a.hammer(LOT_ID);
    }

    /// @dev Arm the FlagRegistry to void the standing top: commit a one-flagged-paddle root (the
    ///      offender == lot.paddleId, the top after _hammerWithTwoBids) with sentinels
    ///      [0, offenderPaddle, MAX] yielding two boundary leaves, and build the candidate plus the
    ///      offender membership proof. Returns the membership proof (the voidAndAward
    ///      flagInclusionProof) and the NextCleanCandidate. Kept separate from the voidAndAward call so
    ///      a caller that vm.expectEmit's LotVoided can arm the tree first, keeping commitFlagRoot's
    ///      FlagRootCommitted out of the expectEmit window.
    ///
    ///      Built proofs (offenderPaddle flagged, candidate strictly bracketed below it):
    ///        - offender membership:     leaf (offenderPaddle, MAX) -> [offenderPaddle, MAX, leafLow]
    ///        - candidate non-membership: bracket (0, offenderPaddle) -> [0, offenderPaddle, leafHigh]
    ///        - precedingFlagInclusion[0]: the one strictly-higher heap slot (the offender) is the
    ///          offender membership proof.
    ///      The candidate paddleId is the real heap paddle (_paddleFor(promoted)); 0 would clear
    ///      NotFlagged but then revert BadCandidate on the e.paddleId mismatch.
    function _armVoidFlagTree(SessionAuction a, address promoted, uint128 promotedAmount, uint40 seq)
        private
        returns (bytes32[] memory memProof, NextCleanCandidate memory cand)
    {
        uint16 SENTINEL = type(uint16).max;
        uint16 offenderPaddle = a.getLot(LOT_ID).paddleId; // the standing top's real KYC paddle
        uint16 candidatePaddle = _paddleFor(promoted);

        // sorted flagged set {offenderPaddle} augmented with sentinels [0, offenderPaddle, MAX] -> two
        // boundary leaves; root = OZ commutative hash of the two leaves. The test contract deployed
        // `flags` in HammerBase.setUp, so it is the FlagRegistry owner and may commit the root.
        bytes32 leafLow  = keccak256(abi.encodePacked(uint16(0), offenderPaddle));    // (0, offender)
        bytes32 leafHigh = keccak256(abi.encodePacked(offenderPaddle, SENTINEL));     // (offender, MAX)
        bytes32 root = leafLow < leafHigh
            ? keccak256(abi.encodePacked(leafLow, leafHigh))
            : keccak256(abi.encodePacked(leafHigh, leafLow));
        flags.commitFlagRoot(SESSION_ID, root); // emits FlagRootCommitted (hence the arm/call split)

        // offender membership (lot.paddleId == offenderPaddle): its leaf is (offenderPaddle, MAX);
        // the sibling is leafLow. low == offenderPaddle satisfies the membership low-endpoint check.
        memProof = new bytes32[](3);
        memProof[0] = bytes32(uint256(offenderPaddle));
        memProof[1] = bytes32(uint256(SENTINEL));
        memProof[2] = leafLow;

        // candidate non-membership: the promoted paddle is unflagged and, with the _paddleFor values,
        // sits below the offender, so the bracket is (0, offenderPaddle) == leafLow and the sibling is
        // leafHigh. Guard the ordering premise so a future actor change fails loudly here.
        require(candidatePaddle < offenderPaddle, "fixture: promoted paddle must sit below the offender for the (0,offender) bracket");
        bytes32[] memory nonMem = new bytes32[](3);
        nonMem[0] = bytes32(uint256(0));
        nonMem[1] = bytes32(uint256(offenderPaddle));
        nonMem[2] = leafHigh;

        // the single strictly-higher heap slot (the offender at 3x reserve, heap slot 1) is flagged.
        bytes32[][] memory preceding = new bytes32[][](1);
        preceding[0] = memProof;

        cand = NextCleanCandidate({
            heapIndex: 0, // cleanBidder bid first in _hammerWithTwoBids -> heap slot 0
            bidder: promoted,
            amount: promotedAmount,
            paddleId: candidatePaddle, // the REAL heap paddle (e.paddleId), not 0
            seq: seq,
            flagNonMembership: nonMem,
            precedingFlagInclusion: preceding
        });
    }

    /// @dev voidAndAward promoting `promoted` against the REAL FlagRegistry (arms the flag tree then
    ///      calls the void). For callers that vm.expectEmit the LotVoided event, arm the tree with
    ///      _armVoidFlagTree BEFORE the expectEmit and call voidAndAward directly, so FlagRootCommitted
    ///      does not fall inside the expectEmit window.
    function _voidAndAward(
        SessionAuction a,
        address promoted,
        uint128 promotedAmount,
        uint40 seq
    ) private {
        (bytes32[] memory memProof, NextCleanCandidate memory cand) =
            _armVoidFlagTree(a, promoted, promotedAmount, seq);

        vm.prank(ops);
        a.voidAndAward(LOT_ID, memProof, cand); // memProof == the offender membership flagInclusionProof
    }

    /// @dev Deposit `amount` into the (lotId, principal) deposit on either rail.
    function _deposit(SessionAuction a, address paymentToken, address principal, uint256 amount) private {
        if (paymentToken == address(0)) {
            vm.prank(principal);
            a.depositCeiling{value: amount}(LOT_ID, amount);
        } else {
            vm.prank(principal);
            token.approve(address(a), amount);
            vm.prank(principal);
            a.depositCeiling(LOT_ID, amount);
        }
    }

    /// @dev A canonical Ceiling envelope bound to `principal` with the contract-derived nonceKey.
    function _ceiling(address principal, bytes32 ceilingCommit) private view returns (Ceiling memory) {
        return Ceiling({
            principal: principal,
            sessionId: SESSION_ID,
            lotId: LOT_ID,
            ceilingCommit: ceilingCommit,
            strategy: 0, // incremental
            deadline: uint64(block.timestamp + 7 days),
            maxBids: uint64(MAX_EXTENSIONS) + 8,
            nonceKey: uint192(uint256(keccak256(abi.encode(SESSION_ID, LOT_ID, principal))))
        });
    }

    /// @dev A REAL attestation quote signed by the seeded operator key over the canonical digest.
    function _quote(Ceiling memory c, uint128 amount, uint64 bidIndex, uint128 observedPrevTop, bytes32 nonce) private view returns (AttestationQuote memory) {
        return _realQuote(c, LOT_ID, amount, bidIndex, observedPrevTop, nonce);
    }

    /// @dev The keyId of the seeded operator key from _defaultInitConfig.
    function _operatorKeyId() private view returns (bytes32) {
        return _baseOperatorKeyId();
    }

    /// @dev Mock PaddleRegistry.paddleOf(principal) -> a nonzero KYC paddle. placeBid reverts
    ///      Unauthorized when paddleOf == 0 (before the BidTooLow and InsufficientFreeBalance checks),
    ///      so every bid needs this mock to clear the KYC gate. Each principal gets a distinct nonzero
    ///      paddle so the hot-slot lot.paddleId tracks the actual bidder.
    function _mockPaddle(address principal, uint16 paddleId) private {
        vm.mockCall(
            address(paddles),
            abi.encodeWithSelector(IPaddleRegistry.paddleOf.selector, principal),
            abi.encode(paddleId)
        );
    }

    /// @dev A stable distinct nonzero paddle for `principal` (deterministic, never 0). Folding the
    ///      address into the low 15 bits then OR-ing 0x8000 keeps the result in [0x8000, 0xFFFF], so
    ///      it can never collapse to paddle 0 (the unregistered sentinel) for any principal.
    function _paddleFor(address principal) private pure returns (uint16) {
        return uint16(uint256(uint160(principal)) & 0x7FFF) | 0x8000;
    }

    /// @dev EIP-712 sign a Ceiling against clone `a`'s self-correcting domain (chainId + clone addr).
    function _signCeiling(SessionAuction a, uint256 pk, Ceiling memory c) private view returns (bytes memory) {
        bytes32 domainSeparator = keccak256(
            abi.encode(
                EIP712_DOMAIN_TYPEHASH,
                keccak256(bytes("Hammer")),
                keccak256(bytes("1")),
                block.chainid,
                address(a)
            )
        );
        bytes32 structHash = keccak256(
            abi.encode(
                CEILING_TYPEHASH,
                c.principal,
                c.sessionId,
                c.lotId,
                c.ceilingCommit,
                c.strategy,
                c.deadline,
                c.maxBids,
                c.nonceKey
            )
        );
        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash));
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(pk, digest);
        return abi.encodePacked(r, s, v);
    }

    /// @dev The whole lifecycle for one rail: Open -> Hammered -> Awaiting -> Delivered -> Released,
    ///      asserting the phase walk, the deliveryState walk, exact seller / fee payouts, slack
    ///      reclaim, and five-bucket conservation of the session denomination.
    function _fullLifecycle(address paymentToken) private {
        // Reset the clock to the forge default so each rail is an independent walk on an identical
        // clock: the two rails run back-to-back and the ERC-20 rail's absolute-time anchors (session
        // window, endsAt, AC + reveal windows) would otherwise read the clock the native rail advanced.
        // The already-settled native session is a separate clone and is untouched.
        vm.warp(1);

        SessionAuction a = _initSession(paymentToken);

        // Rail-scaled reserve base: native uses RESERVE_PRICE (1e18), the 6-decimal ERC-20 rail uses
        // 1e6 (a 1e18 base overflows the winner's INITIAL_TOKEN of 1e12). Every derived amount (bid ==
        // 2x reserve, slack == 1x reserve, fee == bid*feeBps/1e4) divides exactly on both rails, so the
        // conservation and payout assertions below hold identically modulo decimals.
        uint96 reserve = uint96(_reserveFor(paymentToken));

        // deposit more than the bid so slack is reclaimable at the end.
        uint128 bidAmount = uint128(reserve) * 2;
        uint256 depositAmount = uint256(bidAmount) + uint256(reserve); // bidAmount + slack
        uint64 endsAt = uint64(block.timestamp + 1 days);

        vm.prank(address(hammer));
        a.openLot(LOT_ID, seller, reserve, endsAt);

        _deposit(a, paymentToken, winner, depositAmount);

        // conservation snapshot AFTER the deposit is funded into the contract (the only inflow).
        uint256 sellerBefore   = _bal(paymentToken, seller);
        uint256 feeBefore      = _bal(paymentToken, houseFeeRecipient);
        uint256 winnerBefore   = _bal(paymentToken, winner);
        uint256 contractBefore = _bal(paymentToken, address(a));

        // place the winning bid.
        bytes32 salt = keccak256("happy-salt");
        uint128 maxBid = bidAmount;
        bytes32 ceilingCommit = keccak256(abi.encode(maxBid, salt));
        Ceiling memory c = _ceiling(winner, ceilingCommit);
        bytes memory sig = _signCeiling(a, winnerPk, c);
        AttestationQuote memory q = _quote(c, bidAmount, 0, uint128(0), keccak256("qn-full-lifecycle"));
        // placeBid's KYC gate: mock the winner's nonzero paddle so the bid clears the gate.
        _mockPaddle(winner, _paddleFor(winner));

        // confirm the seq-1 BidPlaced event fires, not only the lifecycle/settlement events.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.BidPlaced(LOT_ID, winner, bidAmount, 1);
        vm.prank(winner);
        a.placeBid(c, LOT_ID, winner, 0, bidAmount, sig, _operatorKeyId(), q);

        // hammer.
        vm.warp(uint256(endsAt) + 1);
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Hammered(LOT_ID, winner, bidAmount);
        a.hammer(LOT_ID);
        assertEq(uint256(a.getLot(LOT_ID).phase), uint256(LotPhase.Hammered), "Open->Hammered");

        // post-hammer provenance root.
        vm.prank(settler);
        a.commitBidBook(LOT_ID, keccak256("root"));

        // close the AC window + reveal gate, then finalize.
        Lot memory hammered = a.getLot(LOT_ID);
        vm.warp(uint256(hammered.hammeredAt) + AC_CHALLENGE_SEC + REVEAL_DEADLINE_SEC + 1);
        a.finalizeWinner(LOT_ID);

        {
            Lot memory fin = a.getLot(LOT_ID);
            assertEq(uint256(fin.phase), uint256(LotPhase.Awaiting), "Hammered->Awaiting");
            assertEq(uint256(fin.deliveryState), uint256(DeliveryState.AwaitingDelivery), "AwaitingDelivery");
        }

        // seller marks delivered.
        vm.prank(seller);
        a.markDelivered(LOT_ID, keccak256("delivery-proof"), "ipfs://delivery");
        assertEq(uint256(a.getLot(LOT_ID).deliveryState), uint256(DeliveryState.Delivered), "Delivered");
        // markDelivered sets the deliveredAt anchor the dispute / auto-release window depends on.
        assertEq(uint256(a.getLot(LOT_ID).deliveredAt), block.timestamp, "deliveredAt frozen at markDelivered");

        // buyer confirms receipt -> Released in the same call; seller paid escrow - fee, house paid fee.
        uint256 fee = (uint256(bidAmount) * FEE_BPS) / 10_000;
        uint256 proceeds = uint256(bidAmount) - fee;

        // confirmReceipt emits Confirmed then _release emits Released, checked in order.
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Confirmed(LOT_ID, keccak256("receipt-photo"), "ipfs://photo");
        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.Released(LOT_ID, seller, proceeds, fee);
        vm.prank(winner);
        a.confirmReceipt(LOT_ID, keccak256("receipt-photo"), "ipfs://photo");

        {
            Lot memory rel = a.getLot(LOT_ID);
            assertEq(uint256(rel.phase), uint256(LotPhase.Settled), "Delivered->Settled");
            assertEq(uint256(rel.deliveryState), uint256(DeliveryState.Released), "Released");
            // single-exit: _release zeroes lot.escrowAmount so no second _release / withdrawRefund
            // can double-pay the same escrow.
            assertEq(uint256(rel.escrowAmount), 0, "escrow zeroed on release (single-exit, no double-pay)");
        }

        // winner reclaims the free slack (deposit - bid) once their committed was snapshotted away.
        uint256 slack = depositAmount - uint256(bidAmount);
        assertEq(a.withdrawableFree(LOT_ID, winner), slack, "free slack withdrawable");
        vm.prank(winner);
        a.withdrawDeposit(LOT_ID, slack);

        // Exact balances.
        assertEq(_bal(paymentToken, seller),            sellerBefore + proceeds, "seller paid escrow - fee");
        assertEq(_bal(paymentToken, houseFeeRecipient), feeBefore + fee,         "feeRecipient paid fee");
        assertEq(_bal(paymentToken, winner),            winnerBefore + slack,    "winner reclaimed slack");

        // Conservation: every bucket out reconstructs the escrow that flowed through the contract.
        // proceeds + fee + slack == depositAmount, and the contract is drained of this lot's funds (a
        // successful EOA push to funded actors leaves no pending credit).
        assertEq(proceeds + fee + slack, depositAmount, "payouts reconstruct the deposit (conservation)");
        assertEq(_bal(paymentToken, address(a)), contractBefore - depositAmount, "contract drained by exactly the deposit");
        assertEq(a.pendingWithdrawal(seller),           0, "no stranded pending credit (seller)");
        assertEq(a.pendingWithdrawal(houseFeeRecipient), 0, "no stranded pending credit (fee)");
        assertEq(a.pendingWithdrawal(winner),           0, "no stranded pending credit (winner)");
    }

    /// @dev The rail-appropriate reserve base: RESERVE_PRICE (1e18) for native, TOKEN_RESERVE (1e6)
    ///      for the 6-decimal ERC-20 rail, so the happy path runs "identical modulo decimals".
    function _reserveFor(address paymentToken) private pure returns (uint256) {
        return paymentToken == address(0) ? uint256(RESERVE_PRICE) : TOKEN_RESERVE;
    }

    /// @dev Balance on either rail (native ETH or the 6-decimal MockERC20).
    function _bal(address paymentToken, address who) private view returns (uint256) {
        return paymentToken == address(0) ? who.balance : token.balanceOf(who);
    }
}
