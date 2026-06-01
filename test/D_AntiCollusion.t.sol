// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// End-to-end tests for the anti-collusion void path. When the hammered winner's KYC paddle is
// proven flagged within the post-hammer challenge window, voidAndAward captures the offender's
// escrow as a forfeit, promotes the highest unflagged heap slot to winner (paying its own bid),
// and routes the forfeit to the Treasury waterfall. Covers the void gates, candidate soundness,
// fund safety, the Treasury forfeit lifecycle (deposit, disburse, challenge, resolve), and the
// distinct-paddle heap behavior the void relies on.
//
// Cross-contract dependencies (PaddleRegistry.paddleOf, FlagRegistry.verifyMembership /
// verifyNonMembership) are mocked via vm.mockCall so the SessionAuction void path runs in isolation.

import {HammerBase} from "./HammerBase.t.sol";

import {SessionAuction} from "../src/SessionAuction.sol";
import {Clones} from "@openzeppelin/contracts/proxy/Clones.sol";

import {ISessionAuction} from "../src/interfaces/ISessionAuction.sol";
import {ITreasury}       from "../src/interfaces/ITreasury.sol";
import {IFlagRegistry}   from "../src/interfaces/IFlagRegistry.sol";
import {IPaddleRegistry} from "../src/interfaces/IPaddleRegistry.sol";

import {Pausable} from "@openzeppelin/contracts/utils/Pausable.sol";
import {SafeERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import {IERC20Errors} from "@openzeppelin/contracts/interfaces/draft-IERC6093.sol";
import {ReentrancyGuardTransient} from "@openzeppelin/contracts/utils/ReentrancyGuardTransient.sol";

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

contract AntiCollusionTest is HammerBase {
    // Fixture constants.
    uint256 private constant LOT = 1;

    // Distinct KYC paddles (nonzero == registered). Offender is the highest amount + flagged;
    // candidate is the next-highest + clean. Extra paddles fill the top-5 heap.
    uint16 private constant PADDLE_OFFENDER = 700; // top bid, flagged
    uint16 private constant PADDLE_CLEAN    = 600; // next-clean candidate
    uint16 private constant PADDLE_C3       = 500;
    uint16 private constant PADDLE_C4       = 400;
    uint16 private constant PADDLE_C5       = 300;
    uint16 private constant PADDLE_C6       = 800; // 6th distinct paddle (heap min-replace tests)

    // Bid amounts (native rail; descending). Offender clears highest, candidate is next.
    uint128 private constant AMT_OFFENDER = 100 ether; // offender clearing price == escrow at void
    uint128 private constant AMT_CLEAN    = 80 ether;  // promoted price (their own money)
    uint128 private constant AMT_C3       = 60 ether;
    uint128 private constant AMT_C4       = 40 ether;
    uint128 private constant AMT_C5       = 20 ether;

    // Deposit each bidder pre-funds (slack above their bid hides the ceiling).
    uint256 private constant BIG_DEPOSIT = 200 ether;

    // ERC-20 rail mirrors (6-decimal token; same accounting modulo decimals). INITIAL_TOKEN
    // is 1_000_000e6, so a 200e6 deposit per bidder fits.
    uint128 private constant AMT_OFFENDER_T = 100e6;
    uint128 private constant AMT_CLEAN_T    = 80e6;
    uint128 private constant AMT_C3_T       = 60e6;
    uint128 private constant AMT_C4_T       = 40e6;
    uint128 private constant AMT_C5_T       = 20e6;
    uint256 private constant BIG_DEPOSIT_T  = 200e6;

    // Treasury waterfall defaults: disruption rebate 1%, house fee 20% of the remainder.
    uint16 private constant DISRUPTION_REBATE_BPS = 100;
    uint16 private constant HOUSE_FEE_BPS         = 2000;

    address private relayer;     // non-privileged submitter (proves permissionless)
    address private offender;    // top bidder (gets voided)
    address private cleanBidder; // next-clean (gets promoted)
    address private neutralSink; // forfeit sink

    // EIP-712 domain constants for a clone: EIP712("Hammer","1") bound to the clone address.
    // placeBid recovers the ceiling signature against this domain to the principal.
    bytes32 private constant EIP712_TYPE_HASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 private constant HASHED_NAME = keccak256(bytes("Hammer"));
    bytes32 private constant HASHED_VERSION = keccak256(bytes("1"));

    // principal -> its bound signing key, so _signCeiling can produce a ceiling signature that
    // recovers to the principal. Populated by _bindSigner. placeBid recovers against the `principal`
    // calldata arg, so the key must belong to that principal or placeBid reverts BadSignature.
    mapping(address principal => uint256 signerKey) private _signerKey;

    // Lower heap occupants, set by the ring builders, so candidate calldata can match the exact
    // stored slot.
    address private ringB3;
    address private ringB4;
    address private ringB5;
    address private ringB6; // 6th distinct paddle, set by _buildHammeredRing6On

    function setUp() public override {
        super.setUp();

        relayer     = makeAddr("relayer");
        // Bidding principals carry a bound signing key so their ceiling sig recovers to them.
        offender    = _bindSigner("offender");
        cleanBidder = _bindSigner("cleanBidder");
        neutralSink = makeAddr("neutralSink");
        // bidder1 (a HammerBase actor) bids here too; bind its key from the same stable label.
        (, _signerKey[bidder1]) = makeAddrAndKey("bidder1");

        fundEth(relayer, INITIAL_ETH);
        fundEth(offender, INITIAL_ETH);
        fundEth(cleanBidder, INITIAL_ETH);
        fundToken(offender, INITIAL_TOKEN);
        fundToken(cleanBidder, INITIAL_TOKEN);
    }

    /// @dev Create a named principal with a bound signing key registered in _signerKey, so a ceiling
    ///      signed for `account` recovers to `account` in placeBid.
    function _bindSigner(string memory label) private returns (address account) {
        uint256 key;
        (account, key) = makeAddrAndKey(label);
        _signerKey[account] = key;
    }

    // voidAndAward happy path. On a positive flag-membership proof of the winner within the
    // post-hammer challenge window: capture the offender escrow, promote the highest unflagged clean
    // slot, re-bind winnerSeq = candidate.seq, route the forfeit, and emit the true offender.
    function test_VoidAndAwardPromotesNextClean() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        uint64 candidateSeq = 4; // cleanBidder is the 4th ascending bid, so its bid sequence is 4
        NextCleanCandidate memory cand = _cleanCandidate(candidateSeq);

        // LotVoided carries the true offender (pre-promotion highBidder), not the promoted addr.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.LotVoided(LOT, offender, cleanBidder, AMT_CLEAN);

        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Voided), "phase Voided");
        assertEq(lot.voidedAt, uint40(block.timestamp), "voidedAt set");
        assertEq(lot.highBidder, cleanBidder, "highBidder = promoted");
        assertEq(lot.highBid, AMT_CLEAN, "highBid = promoted amount");
        assertEq(lot.paddleId, PADDLE_CLEAN, "paddleId = promoted paddle");
        assertEq(lot.winnerSeq, candidateSeq, "winnerSeq re-bound to candidate.seq");
        assertEq(lot.escrowAmount, AMT_CLEAN, "escrowAmount = promoted bid (own money)");
    }

    // Void/promote driven against the real FlagRegistry merkle tree with real boundary-leaf proofs
    // and no _mockFlagsHappy: the anti-collusion path end-to-end on a deployed FlagRegistry.
    function test_VoidAndAwardWithRealFlagTree() external {
        // Flagged set {PADDLE_OFFENDER=700}; sorted with sentinels [0, 700, max] gives two boundary
        // leaves. root = OZ commutative hash of the two leaves.
        uint16 SENTINEL = type(uint16).max;
        bytes32 leafLow = keccak256(abi.encodePacked(uint16(0), PADDLE_OFFENDER));        // (0, 700)
        bytes32 leafHigh = keccak256(abi.encodePacked(PADDLE_OFFENDER, SENTINEL));        // (700, MAX)
        bytes32 root = leafLow < leafHigh
            ? keccak256(abi.encodePacked(leafLow, leafHigh))
            : keccak256(abi.encodePacked(leafHigh, leafLow));
        flags.commitFlagRoot(SESSION_ID, root); // this test contract deployed `flags`, so it owns it

        _buildHammeredRingNative(); // offender (700) hammered top; cleanBidder (600) at heap slot 3, bid seq 4

        // membership of the offender (700): leaf (700, MAX), sibling the (0,700) leaf.
        bytes32[] memory memProof = new bytes32[](3);
        memProof[0] = bytes32(uint256(PADDLE_OFFENDER));
        memProof[1] = bytes32(uint256(SENTINEL));
        memProof[2] = leafLow;

        // non-membership of the candidate (600): bracketed by (0,700), sibling the (700,MAX) leaf.
        bytes32[] memory nonMem = new bytes32[](3);
        nonMem[0] = bytes32(uint256(0));
        nonMem[1] = bytes32(uint256(PADDLE_OFFENDER));
        nonMem[2] = leafHigh;

        bytes32[][] memory preceding = new bytes32[][](1);
        preceding[0] = memProof; // the one strictly-higher heap slot (offender) is flagged

        NextCleanCandidate memory cand = NextCleanCandidate({
            heapIndex: 3,
            bidder: cleanBidder,
            amount: AMT_CLEAN,
            paddleId: PADDLE_CLEAN,
            seq: 4,
            flagNonMembership: nonMem,
            precedingFlagInclusion: preceding
        });

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.LotVoided(LOT, offender, cleanBidder, AMT_CLEAN);

        vm.prank(relayer);
        auction.voidAndAward(LOT, memProof, cand); // real proofs against the real FlagRegistry

        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Voided), "real-proof void: phase Voided");
        assertEq(lot.highBidder, cleanBidder, "real-proof void: promoted clean candidate");
        assertEq(lot.highBid, AMT_CLEAN, "real-proof void: promoted amount");
    }

    // A flagged paddle must not forge non-membership via dirty high bits: proof[1] = 65536 + realHigh
    // makes the full-width bracket pass (paddleId < high) while uint16(high) rebuilds the real in-tree
    // leaf. The clean-bits guard must reject it.
    function test_RevertWhen_ForgedNonMembershipDirtyHighBits() external {
        uint16 SENTINEL = type(uint16).max;
        bytes32 leafLow = keccak256(abi.encodePacked(uint16(0), PADDLE_OFFENDER)); // (0, 700)
        bytes32 leafHigh = keccak256(abi.encodePacked(PADDLE_OFFENDER, SENTINEL)); // (700, MAX)
        bytes32 root = leafLow < leafHigh
            ? keccak256(abi.encodePacked(leafLow, leafHigh))
            : keccak256(abi.encodePacked(leafHigh, leafLow));
        flags.commitFlagRoot(SESSION_ID, root);

        // Forge non-membership of the flagged paddle 700: bracket (0, 65536+700). uint16(66236)==700 so
        // the leaf is the real (0,700) leaf, but the full-width high (66236) trivially satisfies 700<high.
        bytes32[] memory forged = new bytes32[](3);
        forged[0] = bytes32(uint256(0));
        forged[1] = bytes32(uint256(65536) + uint256(PADDLE_OFFENDER));
        forged[2] = leafHigh;

        assertFalse(
            flags.verifyNonMembership(SESSION_ID, PADDLE_OFFENDER, forged),
            "dirty-high-bits non-membership forgery of a flagged paddle must fail"
        );
    }

    // Offender snapshot and emit ordering. LotVoided.offender equals the pre-promotion highBidder,
    // never the promoted address; the forfeit equals the offender's pre-void escrowAmount (the
    // higher value), never the lower promoted amount.
    function test_VoidEmitsTrueOffenderAndHigherForfeit() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        // Pre-void offender escrow is the offender clearing price (AMT_OFFENDER > AMT_CLEAN).
        assertEq(auction.getLot(LOT).escrowAmount, AMT_OFFENDER, "offender escrow pre-void");

        NextCleanCandidate memory cand = _cleanCandidate(4);

        // Treasury receives offenderEscrow (AMT_OFFENDER), not candidate.amount (AMT_CLEAN):
        // forfeitAmount and offenderClearing both == AMT_OFFENDER, promotedPrice == AMT_CLEAN.
        bytes memory expectedCall = abi.encodeCall(
            ITreasury.depositForfeit,
            (offender, cleanBidder, LOT, uint256(AMT_OFFENDER), uint256(AMT_OFFENDER), uint256(AMT_CLEAN), seller)
        );
        vm.expectCall(address(treasury), expectedCall);

        // LotVoided.offender (topic 2) is the offender, distinct from promotedWinner (topic 3).
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.LotVoided(LOT, offender, cleanBidder, AMT_CLEAN);

        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        assertTrue(offender != cleanBidder, "offender distinct from promoted");
    }

    // Void revert gates. NotHammered (phase != Hammered), AcWindowClosed (window anchored on
    // hammeredAt, callable at +acChallengeSec-1, reverts at +acChallengeSec), NotFlagged
    // (verifyMembership false), EnforcedPause (paused). On any of these no promotion happens and the
    // offender escrow is untouched.
    function test_RevertWhen_VoidNotHammered() external {
        // Open lot, never hammered: phase Open.
        _initNative();
        _openLot();
        NextCleanCandidate memory cand = _cleanCandidate(4);
        _mockFlagsHappy();

        vm.expectRevert(ISessionAuction.NotHammered.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
    }

    function test_RevertWhen_VoidAcWindowClosed() external {
        _buildHammeredRingNative();
        NextCleanCandidate memory cand = _cleanCandidate(4);

        // Boundary: at hammeredAt + acChallengeSec (window is [hammeredAt, hammeredAt+sec)).
        uint40 hammeredAt = auction.getLot(LOT).hammeredAt;
        vm.warp(uint256(hammeredAt) + AC_CHALLENGE_SEC);

        // A closed window must route no forfeit; snapshot Treasury to catch a capture/route that
        // runs before the window check.
        uint256 treasuryBefore = address(treasury).balance;

        vm.expectRevert(ISessionAuction.AcWindowClosed.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // No side effect: offender still the provisional winner, escrow intact, no forfeit routed.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Hammered), "stays Hammered after AcWindowClosed");
        assertEq(lot.highBidder, offender, "offender still highBidder after AcWindowClosed");
        assertEq(lot.escrowAmount, AMT_OFFENDER, "offender escrow untouched after AcWindowClosed");
        assertEq(address(treasury).balance, treasuryBefore, "no forfeit routed past the closed window");
    }

    function test_VoidCallableAtWindowEdge() external {
        // At +acChallengeSec-1 (the last instant of the half-open window) the void is still callable.
        // Off-by-one twin of test_RevertWhen_VoidAcWindowClosed (which warps to +acChallengeSec).
        // Flags must be mocked happy or the path reverts NotFlagged before the boundary is exercised.
        _buildHammeredRingNative();
        _mockFlagsHappy();
        NextCleanCandidate memory cand = _cleanCandidate(4);

        uint40 hammeredAt = auction.getLot(LOT).hammeredAt;
        vm.warp(uint256(hammeredAt) + AC_CHALLENGE_SEC - 1);

        // Pin the forfeit money-move (native value + exact 7-arg calldata) at the last legal instant,
        // not merely the lot mutation + emit, so a promote-without-routing at the boundary is caught.
        uint256 treasuryBefore = address(treasury).balance;
        vm.expectCall(
            address(treasury),
            uint256(AMT_OFFENDER),
            abi.encodeCall(
                ITreasury.depositForfeit,
                (offender, cleanBidder, LOT, uint256(AMT_OFFENDER), uint256(AMT_OFFENDER), uint256(AMT_CLEAN), seller)
            )
        );

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.LotVoided(LOT, offender, cleanBidder, AMT_CLEAN);

        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // The void fully took at the last legal instant, not merely emitted.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Voided), "edge: phase Voided");
        assertEq(lot.voidedAt, uint40(block.timestamp), "edge: voidedAt = now (= hammeredAt+sec-1)");
        assertEq(lot.highBidder, cleanBidder, "edge: highBidder = promoted");
        assertEq(lot.escrowAmount, AMT_CLEAN, "edge: escrowAmount = promoted own bid");
        // The forfeit moved at the boundary: Treasury grew by exactly the offender escrow.
        assertEq(
            address(treasury).balance - treasuryBefore,
            AMT_OFFENDER,
            "edge: forfeit routed (Treasury grows by offenderEscrow) at +sec-1"
        );
    }

    function test_RevertWhen_VoidNotFlagged() external {
        _buildHammeredRingNative();
        NextCleanCandidate memory cand = _cleanCandidate(4);

        // verifyMembership returns false for the winner's paddle (empty/garbage proof): NotFlagged.
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector, SESSION_ID, PADDLE_OFFENDER),
            abi.encode(false)
        );

        vm.expectRevert(ISessionAuction.NotFlagged.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, new bytes32[](0), cand);

        // No side effect: offender still the provisional winner, escrow intact.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Hammered), "stays Hammered after NotFlagged");
        assertEq(lot.highBidder, offender, "offender still highBidder after NotFlagged");
        assertEq(lot.escrowAmount, AMT_OFFENDER, "offender escrow untouched after NotFlagged");
    }

    function test_RevertWhen_VoidPaused() external {
        _buildHammeredRingNative();
        NextCleanCandidate memory cand = _cleanCandidate(4);

        vm.prank(pauser);
        auction.pause();

        // A paused void must forfeit nothing; snapshot Treasury to catch a whenNotPaused guard that
        // sits after capture/route.
        uint256 treasuryBefore = address(treasury).balance;

        vm.expectRevert(Pausable.EnforcedPause.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // No side effect while paused: offender still the provisional winner, escrow intact.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Hammered), "stays Hammered while paused");
        assertEq(lot.highBidder, offender, "offender still highBidder while paused");
        assertEq(lot.escrowAmount, AMT_OFFENDER, "offender escrow untouched while paused");
        assertEq(address(treasury).balance, treasuryBefore, "no forfeit routed while paused");
    }

    // voidAndAward is permissionless. A non-privileged caller with a valid proof (unpaused) succeeds;
    // there is no msg.sender role gate. pause/unpause remain onlyPauser.
    function test_VoidAndAwardPermissionless() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();
        NextCleanCandidate memory cand = _cleanCandidate(4);

        // relayer holds no role (not hammer/settler/ops/arbiter/pauser): only the window, the pause
        // state, and the merkle proof gate the void, never a caller-role check.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.LotVoided(LOT, offender, cleanBidder, AMT_CLEAN);

        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // pause stays role-gated: a non-pauser cannot pause.
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        vm.prank(relayer);
        auction.pause();
    }

    // Candidate soundness. A flagged candidate cannot be promoted (verifyNonMembership false ->
    // BadCandidate); a non-membership proof valid for a different paddle is not replayable (the
    // registry binds the bracket/leaf to the claimed paddle).
    function test_RevertWhen_CandidateFlagged() external {
        _buildHammeredRingNative();
        NextCleanCandidate memory cand = _cleanCandidate(4);

        // Offender paddle is flagged (membership true, so the void gate passes), but the candidate
        // paddle is ALSO flagged: verifyNonMembership returns false -> BadCandidate.
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector, SESSION_ID, PADDLE_OFFENDER),
            abi.encode(true)
        );
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyNonMembership.selector, SESSION_ID, PADDLE_CLEAN),
            abi.encode(false)
        );

        // The capture zeroes lot.escrowAmount before the candidate guard runs, so a BadCandidate
        // revert must unwind the capture and route no forfeit. Snapshot Treasury to catch a
        // capture/route that survives the revert.
        uint256 treasuryBefore = address(treasury).balance;

        vm.expectRevert(ISessionAuction.BadCandidate.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // The whole tx unwound: offender still the provisional winner, escrow intact, no forfeit.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Hammered), "stays Hammered after BadCandidate (flagged candidate)");
        assertEq(lot.highBidder, offender, "offender still highBidder after BadCandidate (flagged candidate)");
        assertEq(lot.escrowAmount, AMT_OFFENDER, "offender escrow untouched after BadCandidate (flagged candidate)");
        assertEq(address(treasury).balance, treasuryBefore, "no forfeit routed on BadCandidate (flagged candidate)");
    }

    function test_RevertWhen_NonMembershipProofReplayed() external {
        _buildHammeredRingNative();

        // A non-membership proof valid for PADDLE_C3 is supplied for the candidate slot whose
        // paddle is PADDLE_CLEAN. The FlagRegistry pins low < p < high to the CLAIMED paddle, so
        // a proof minted for a different paddle does not verify for PADDLE_CLEAN -> BadCandidate.
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector, SESSION_ID, PADDLE_OFFENDER),
            abi.encode(true)
        );
        // verifyNonMembership(PADDLE_C3) would be true, but the candidate claims PADDLE_CLEAN:
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyNonMembership.selector, SESSION_ID, PADDLE_C3),
            abi.encode(true)
        );
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyNonMembership.selector, SESSION_ID, PADDLE_CLEAN),
            abi.encode(false)
        );

        NextCleanCandidate memory cand = _cleanCandidate(4); // paddleId == PADDLE_CLEAN

        // The candidate guard rejects the replayed proof; the earlier escrow capture must not survive
        // the revert.
        uint256 treasuryBefore = address(treasury).balance;

        vm.expectRevert(ISessionAuction.BadCandidate.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // Lot untouched (still Hammered, offender still winner, escrow intact), no forfeit routed.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Hammered), "stays Hammered after BadCandidate (replayed proof)");
        assertEq(lot.highBidder, offender, "offender still highBidder after BadCandidate (replayed proof)");
        assertEq(lot.escrowAmount, AMT_OFFENDER, "offender escrow untouched after BadCandidate (replayed proof)");
        assertEq(address(treasury).balance, treasuryBefore, "no forfeit routed on BadCandidate (replayed proof)");
    }

    // Canonical next-clean (no skipping a higher clean bid). _verifyAndPromote requires every
    // strictly-higher-amount heap slot to be provably flagged via precedingFlagInclusion[k];
    // skipping an unflagged higher bid reverts BadCandidate.
    function test_RevertWhen_CandidateSkipsHigherCleanBid() external {
        _buildHammeredRingNative();

        // ringB3 sits at heapIndex 2 (PADDLE_C3, AMT_C3, _bidSeq 3), but a strictly-higher slot
        // (PADDLE_CLEAN @ AMT_CLEAN) is NOT flagged: the canonical next-clean is PADDLE_CLEAN, so
        // promoting C3 over an unflagged higher bid must revert BadCandidate.
        NextCleanCandidate memory cand = _candidate(2, ringB3, AMT_C3, PADDLE_C3, 3);

        // Offender flagged (membership ok); candidate C3 itself clean (non-membership ok)...
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector, SESSION_ID, PADDLE_OFFENDER),
            abi.encode(true)
        );
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyNonMembership.selector, SESSION_ID, PADDLE_C3),
            abi.encode(true)
        );
        // ...but the strictly-higher PADDLE_CLEAN is NOT flagged, so the precedingFlagInclusion
        // membership proof for it must fail.
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector, SESSION_ID, PADDLE_CLEAN),
            abi.encode(false)
        );

        // The skip guard rejects this; the earlier escrow capture must not survive the revert.
        uint256 treasuryBefore = address(treasury).balance;

        vm.expectRevert(ISessionAuction.BadCandidate.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // Lot untouched (still Hammered, offender still winner, escrow intact), no forfeit routed.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Hammered), "stays Hammered after BadCandidate (skipped higher clean)");
        assertEq(lot.highBidder, offender, "offender still highBidder after BadCandidate (skipped higher clean)");
        assertEq(lot.escrowAmount, AMT_OFFENDER, "offender escrow untouched after BadCandidate (skipped higher clean)");
        assertEq(address(treasury).balance, treasuryBefore, "no forfeit routed on BadCandidate (skipped higher clean)");
    }

    // Calldata-vs-heap match and empty-slot guards. BadCandidate if heapIndex >= 5 or any of
    // (bidder, amount, paddleId, seq) mismatches the stored slot; NotPromotable if the named slot
    // is empty (bidder == 0 or amount == 0).
    function test_RevertWhen_CandidateMismatchesHeap() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        // heapIndex out of range (>= 5): BadCandidate, before any flag proof or mutation.
        NextCleanCandidate memory bad = _cleanCandidate(4);
        bad.heapIndex = 5;

        // The range guard rejects this; the earlier escrow capture must not survive the revert.
        uint256 treasuryBefore = address(treasury).balance;

        vm.expectRevert(ISessionAuction.BadCandidate.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), bad);

        // Lot untouched (still Hammered, offender still winner, escrow intact), no forfeit routed.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Hammered), "stays Hammered after BadCandidate (heapIndex out of range)");
        assertEq(lot.highBidder, offender, "offender still highBidder after BadCandidate (heapIndex out of range)");
        assertEq(lot.escrowAmount, AMT_OFFENDER, "offender escrow untouched after BadCandidate (heapIndex out of range)");
        assertEq(address(treasury).balance, treasuryBefore, "no forfeit routed on BadCandidate (heapIndex out of range)");
    }

    function test_RevertWhen_CandidateFieldMismatchesHeap() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        // Valid heapIndex but the amount field does not match the stored slot: BadCandidate.
        NextCleanCandidate memory bad = _cleanCandidate(4);
        bad.amount = AMT_CLEAN + 1 ether;

        // The field-match guard rejects this; the earlier escrow capture must not survive the revert.
        uint256 treasuryBefore = address(treasury).balance;

        vm.expectRevert(ISessionAuction.BadCandidate.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), bad);

        // Lot untouched (still Hammered, offender still winner, escrow intact), no forfeit routed.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Hammered), "stays Hammered after BadCandidate (field mismatch)");
        assertEq(lot.highBidder, offender, "offender still highBidder after BadCandidate (field mismatch)");
        assertEq(lot.escrowAmount, AMT_OFFENDER, "offender escrow untouched after BadCandidate (field mismatch)");
        assertEq(address(treasury).balance, treasuryBefore, "no forfeit routed on BadCandidate (field mismatch)");
    }

    function test_RevertWhen_CandidateSlotEmpty() external {
        // Only the offender bid: heap slot index 1 is empty (bidder == 0, amount == 0).
        _initNative();
        _openLot();
        _mockPaddle(offender, PADDLE_OFFENDER);
        _depositNative(offender, BIG_DEPOSIT);
        _placeBidNative(offender, 0, AMT_OFFENDER, PADDLE_OFFENDER, 0);
        _hammerLot();
        _mockFlagsHappy();

        // candidate points at an unfilled slot: NotPromotable.
        NextCleanCandidate memory cand = _candidate(1, address(0), 0, 0, 0);

        vm.expectRevert(ISessionAuction.NotPromotable.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
    }

    // All top-N flagged. With every heap slot flagged no clean candidate exists; forcing the top
    // slot through reverts BadCandidate, the lot stays Hammered, no forfeit, no promotion (the
    // operator must escalate to voidSession).
    function test_RevertWhen_AllTopNFlagged() external {
        _buildHammeredRingNative();

        uint256 treasuryBefore = address(treasury).balance; // no forfeit must be routed on revert

        // Every heap occupant's paddle is flagged: any candidate's verifyNonMembership is false.
        vm.mockCall(address(flags), abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector), abi.encode(true));
        vm.mockCall(address(flags), abi.encodeWithSelector(IFlagRegistry.verifyNonMembership.selector), abi.encode(false));

        // Even the top clean-looking slot is flagged, so forcing it through reverts BadCandidate.
        NextCleanCandidate memory cand = _cleanCandidate(4);

        vm.expectRevert(ISessionAuction.BadCandidate.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // Lot unchanged (still Hammered, offender still highBidder, escrow intact).
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Hammered), "lot stays Hammered");
        assertEq(lot.highBidder, offender, "offender still winner");
        assertEq(lot.escrowAmount, AMT_OFFENDER, "offender escrow untouched");
        // No forfeit routed: capture/route did not run before the promotion reverted.
        assertEq(address(treasury).balance, treasuryBefore, "no forfeit routed when NotPromotable");
    }

    // Underfunded promoted candidate. _relockPromoted reverts InsufficientFreeBalance when the
    // candidate withdrew their free below the promoted amount; the whole tx unwinds (offender
    // escrow not routed), and the submitter must supply the next clean index.
    function test_RevertWhen_PromotedCandidateWithdrewSlack() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        // The clean candidate withdraws below their bid after being outbid, losing promotion
        // eligibility; _relockPromoted (free -> committed) will revert.
        vm.prank(cleanBidder);
        auction.withdrawDeposit(LOT, BIG_DEPOSIT); // drains free to 0

        NextCleanCandidate memory cand = _cleanCandidate(4);

        // When _relockPromoted reverts the whole tx must unwind, leaving the offender escrow unrouted;
        // snapshot Treasury to catch a relock that reverts after the capture already ran.
        uint256 treasuryBefore = address(treasury).balance;

        vm.expectRevert(ISessionAuction.InsufficientFreeBalance.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // The whole void unwound: lot still Hammered, offender still winner, escrow intact, no forfeit.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Hammered), "stays Hammered when the relock reverts (drained slack)");
        assertEq(lot.highBidder, offender, "offender still winner when the relock reverts (drained slack)");
        assertEq(lot.escrowAmount, AMT_OFFENDER, "offender escrow untouched when the relock reverts (drained slack)");
        assertEq(address(treasury).balance, treasuryBefore, "no forfeit routed when the relock reverts (drained slack)");
    }

    // Promoted winner pays their OWN bid (no windfall). _relockPromoted moves free -> committed for
    // candidate.amount, then _lockEscrow re-snapshots it into escrowAmount; the candidate does not
    // get the lot for free, and the seller is later paid from this escrow at delivery.
    function test_PromotedWinnerPaysOwnBid() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        uint256 freeBefore = auction.withdrawableFree(LOT, cleanBidder);
        assertEq(freeBefore, BIG_DEPOSIT, "promoted free starts at full deposit (was outbid)");

        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // Free fell by exactly the promoted amount; escrow holds their own money.
        uint256 freeAfter = auction.withdrawableFree(LOT, cleanBidder);
        assertEq(freeBefore - freeAfter, AMT_CLEAN, "promoted free debited by own bid");
        assertEq(auction.getLot(LOT).escrowAmount, AMT_CLEAN, "escrow = promoted own bid");
    }

    // _captureForfeit reads escrowAmount, not committed. Post-hammer the offender funds sit in
    // lot.escrowAmount (committed already zeroed by hammer); reading committed would route 0 and
    // strand the offender. forfeitAmount == captured escrow.
    function test_CaptureForfeitReadsEscrowNotCommitted() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        // Post-hammer the offender's committed is 0 (hammer moved it into escrowAmount).
        assertEq(auction.getLot(LOT).escrowAmount, AMT_OFFENDER, "offender escrow = clearing price");

        // The forfeit equals the captured escrowAmount (AMT_OFFENDER), never 0 (committed) nor the
        // lower promoted amount.
        vm.expectCall(
            address(treasury),
            abi.encodeCall(
                ITreasury.depositForfeit,
                (offender, cleanBidder, LOT, uint256(AMT_OFFENDER), uint256(AMT_OFFENDER), uint256(AMT_CLEAN), seller)
            )
        );

        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
    }

    // Capture-before-promote ordering (no clobber or strand). _captureForfeit runs before
    // _verifyAndPromote/_lockEscrow re-locks the same escrowAmount slot; the offender escrow is held
    // in a local and routed out, the slot ends at candidate.amount, and no wei is stranded.
    function test_CaptureBeforePromoteOrdering() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        uint256 treasuryBefore = address(treasury).balance;
        uint256 cloneBefore = address(auction).balance; // the forfeit is the only transfer out

        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // After the void: escrowAmount holds the re-locked promoted bid, not the offender clearing
        // price; the offender's snapshotted escrow went to Treasury.
        assertEq(auction.getLot(LOT).escrowAmount, AMT_CLEAN, "escrow re-set to promoted amount");
        assertEq(
            address(treasury).balance - treasuryBefore,
            AMT_OFFENDER,
            "offender escrow routed out, not clobbered"
        );
        // The clone balance falls by exactly offenderEscrow (the single cross-contract move): the
        // promoted bid only moved free->committed->escrow inside the clone, so the forfeit is the
        // only wei out. No wei stranded, no wei minted.
        assertEq(cloneBefore - address(auction).balance, AMT_OFFENDER, "clone balance falls by exactly offenderEscrow");
    }

    // _routeForfeit -> depositForfeit argument wiring. Passes the offender escrow as both
    // forfeitAmount and offenderClearing, and candidate.amount as promotedPrice; this 7-arg call is
    // the only cross-contract money move in the void path.
    function test_RouteForfeitArgWiring() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        // Exact 7-arg call (offender, promotedWinner, lotId, forfeitAmount, offenderClearing,
        // promotedPrice, seller) forwarding native msg.value == offenderEscrow. The (target, msgValue,
        // calldata, count) overload pins the exactly-once count and msg.value in one registration:
        // msg.value is not part of the calldata, so this catches a void that forwards the wrong native
        // value (or 0).
        vm.expectCall(
            address(treasury),
            uint256(AMT_OFFENDER), // native value forwarded == offenderEscrow
            abi.encodeCall(
                ITreasury.depositForfeit,
                (offender, cleanBidder, LOT, uint256(AMT_OFFENDER), uint256(AMT_OFFENDER), uint256(AMT_CLEAN), seller)
            ),
            uint64(1) // exactly once
        );

        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
    }

    // depositForfeit funds itself per rail. Native asserts msg.value == forfeitAmount; ERC-20 pulls
    // safeTransferFrom(token, clone, this, forfeitAmount) and asserts msg.value == 0; either rail
    // stores forfeitAmount as the disburse/challenge basis. Both rails exercised.
    function test_DepositForfeitFundsPerRail() external {
        // Native rail: the clone pushes forfeitAmount as msg.value; Treasury balance grows.
        _buildHammeredRingNative();
        _mockFlagsHappy();
        uint256 nativeBefore = address(treasury).balance;

        NextCleanCandidate memory candN = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), candN);

        assertEq(
            address(treasury).balance - nativeBefore,
            AMT_OFFENDER,
            "native: Treasury funded by exactly forfeitAmount"
        );

        // ERC-20 rail: a fresh session/clone on the token rail pulls forfeitAmount from the
        // clone via safeTransferFrom; msg.value must be 0. Token leaves the clone, lands at Treasury.
        SessionAuction erc20Auction = _erc20HammeredRing();
        _mockFlagsHappy(); // mocks key on the shared `flags` address

        uint256 cloneTokenBefore = token.balanceOf(address(erc20Auction));
        uint256 treasuryTokenBefore = token.balanceOf(address(treasury));

        NextCleanCandidate memory candE = _cleanCandidateToken(4);
        vm.prank(relayer);
        erc20Auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), candE);

        // The forfeit (offender clearing price, token-scaled) is pulled FROM the clone TO Treasury.
        assertEq(
            cloneTokenBefore - token.balanceOf(address(erc20Auction)),
            AMT_OFFENDER_T,
            "erc20: forfeitAmount pulled from clone"
        );
        assertEq(
            token.balanceOf(address(treasury)) - treasuryTokenBefore,
            AMT_OFFENDER_T,
            "erc20: forfeitAmount lands at Treasury"
        );
    }

    // depositForfeit is onlyAuction (factory-registered clone). An unregistered caller cannot
    // deposit a forfeit.
    function test_RevertWhen_DepositForfeitUnregistered() external {
        // A direct call from an unregistered EOA (registerClone never run for it): rejected.
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        vm.prank(relayer);
        treasury.depositForfeit{value: AMT_OFFENDER}(
            offender, cleanBidder, LOT, AMT_OFFENDER, AMT_OFFENDER, AMT_CLEAN, seller
        );
    }

    // Treasury disburse waterfall split order. sellerMakeWhole =
    // min(forfeitAmount, offenderClearing - promotedPrice) to the seller FIRST; then over the
    // remainder: rebate = min(remainder*rebateBps/1e4, cap) to the promoted winner; house =
    // remainder*houseFeeBps/1e4 to the feeRecipient; the rest to the neutral sink. The components
    // sum to forfeitAmount.
    function test_DisburseWaterfallSplit() external {
        // Create the forfeit via a real void (forfeitAmount == AMT_OFFENDER, offenderClearing ==
        // AMT_OFFENDER, promotedPrice == AMT_CLEAN).
        _buildHammeredRingNative();
        _mockFlagsHappy();

        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        bytes32 forfeitId = _forfeitId(offender, LOT);

        // Past the challenge window, unchallenged: disburse splits the stored forfeitAmount.
        vm.warp(block.timestamp + 30 days);

        // `seller` and the promoted winner (`cleanBidder`) are passed into depositForfeit; the house
        // is the session-configured feeRecipient (_defaultInitConfig.feeRecipient == houseFeeRecipient).
        // The bps below are the configured defaults; the sink share is asserted as the conservation
        // residual so it does not pin an address the Treasury instance cannot know.
        uint256 sellerBefore = seller.balance;
        uint256 promotedBefore = cleanBidder.balance;
        uint256 houseBefore = houseFeeRecipient.balance;
        uint256 treasuryBefore = address(treasury).balance; // the forfeit is the only balance here

        treasury.disburse(forfeitId);

        // Expected split, forfeitAmount == AMT_OFFENDER:
        uint256 makeWhole = AMT_OFFENDER - AMT_CLEAN;          // offenderClearing - promotedPrice
        if (makeWhole > AMT_OFFENDER) makeWhole = AMT_OFFENDER; // min guard
        uint256 remainder = AMT_OFFENDER - makeWhole;
        uint256 rebate = (remainder * DISRUPTION_REBATE_BPS) / 1e4; // assume below cap
        uint256 house = (remainder * HOUSE_FEE_BPS) / 1e4;
        uint256 rest = remainder - rebate - house;

        assertEq(seller.balance - sellerBefore, makeWhole, "seller made whole first");
        assertEq(cleanBidder.balance - promotedBefore, rebate, "promoted gets small rebate");
        assertEq(houseFeeRecipient.balance - houseBefore, house, "house fee to configured feeRecipient");
        // Conservation: every wei of the stored forfeitAmount leaves Treasury (the sink absorbs the
        // residual `rest`), pinning the split total without hardcoding the sink address.
        assertEq(address(treasury).balance, treasuryBefore - AMT_OFFENDER, "entire forfeit disbursed (sink absorbs rest)");
        assertEq(makeWhole + rebate + house + rest, AMT_OFFENDER, "components sum to forfeitAmount");
        // The flagged offender gets nothing back from an unchallenged disburse.
        assertEq(rest, AMT_OFFENDER - makeWhole - rebate - house, "rest is the conserved residual");
    }

    // False-flag-for-profit is net-negative. A colluding underbidder pays their own bid, gets at
    // most the rebate, the seller is made whole first, and the bulk goes to the neutral sink (out
    // of the ring's reach). The promoted underbidder does NOT get the lot for free.
    function test_FalseFlagForProfitIsNetNegative() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        uint256 promotedFreeBefore = auction.withdrawableFree(LOT, cleanBidder);

        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        bytes32 forfeitId = _forfeitId(offender, LOT);

        // The promoted (friendly) underbidder PAID their own bid (no free lot).
        assertEq(
            promotedFreeBefore - auction.withdrawableFree(LOT, cleanBidder),
            AMT_CLEAN,
            "friend paid own bid, no windfall"
        );

        vm.warp(block.timestamp + 30 days);
        uint256 friendBefore = cleanBidder.balance;
        uint256 sellerBefore = seller.balance;
        uint256 treasuryBefore = address(treasury).balance; // only the forfeit sits here

        treasury.disburse(forfeitId);

        uint256 makeWhole = AMT_OFFENDER - AMT_CLEAN;
        uint256 remainder = AMT_OFFENDER - makeWhole;
        uint256 rebate = (remainder * DISRUPTION_REBATE_BPS) / 1e4;
        uint256 rest = remainder - rebate - (remainder * HOUSE_FEE_BPS) / 1e4;

        // The friend's gross payoff is at most the (tiny) rebate; the seller is made whole first; the
        // bulk (`rest`) leaves Treasury to the neutral sink. Conservation pins the sink residual
        // without hardcoding the sink address.
        assertEq(cleanBidder.balance - friendBefore, rebate, "friend gross <= rebate");
        assertEq(seller.balance - sellerBefore, makeWhole, "seller made whole first");
        assertEq(address(treasury).balance, treasuryBefore - AMT_OFFENDER, "bulk left to sink (entire forfeit disbursed)");
        assertGt(rest, 0, "a non-trivial residual is routed out of the ring's reach");
        assertLt(rebate, AMT_CLEAN, "rebate dwarfed by the bid the friend paid (net-negative)");
    }

    // Treasury challenge(forfeitId) is onlyOffender and requires
    // bond >= forfeitAmount*counterBondBps/1e4 (sized against the stored forfeitAmount); it sets
    // challenged = true, which blocks disburse.
    function test_RevertWhen_ChallengeNotOffender() external {
        bytes32 forfeitId = _forfeitId(offender, LOT);

        // A non-offender (the promoted winner) cannot challenge the forfeit.
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        vm.prank(cleanBidder);
        treasury.challenge{value: AMT_OFFENDER}(forfeitId);
    }

    function test_ChallengeBlocksDisburse() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();
        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        bytes32 forfeitId = _forfeitId(offender, LOT);

        // Offender challenges with a sufficient counter-bond: challenged becomes true.
        vm.prank(offender);
        treasury.challenge{value: AMT_OFFENDER}(forfeitId);

        // disburse is blocked while the challenge is open (the arbiter must rule first). ITreasury
        // declares no errors, so this expects AlreadyDisputed (from ISessionAuction).
        vm.warp(block.timestamp + 30 days);
        vm.expectRevert(ISessionAuction.AlreadyDisputed.selector);
        treasury.disburse(forfeitId);
    }

    // Treasury resolveChallenge(forfeitId, offenderWasInnocent) is onlyArbiter. innocent == true
    // returns the offender escrow + counter-bond (the lot stays promoted; v1 does not un-promote);
    // innocent == false forfeits the bond and runs the waterfall.
    function test_RevertWhen_ResolveChallengeNotArbiter() external {
        bytes32 forfeitId = _forfeitId(offender, LOT);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        vm.prank(relayer);
        treasury.resolveChallenge(forfeitId, true);
    }

    function test_ResolveChallengeOutcomes() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();
        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        bytes32 forfeitId = _forfeitId(offender, LOT);

        uint256 counterBond = AMT_OFFENDER; // a sufficient counter-bond
        vm.prank(offender);
        treasury.challenge{value: counterBond}(forfeitId);

        // Pre-resolve Treasury holds the forfeit (AMT_OFFENDER) plus the counter-bond (AMT_OFFENDER).
        // On the overturned flag both return to the offender and nothing is split out, so Treasury
        // ends at 0.
        assertEq(address(treasury).balance, uint256(AMT_OFFENDER) + counterBond, "innocent: Treasury holds forfeit + bond pre-resolve");

        // Innocent == true: escrow + counter-bond returned to the offender; the lot stays promoted
        // (v1 does not un-promote). The void is unwound at the Treasury layer, so the seller-make-whole
        // waterfall must NOT run; the seller delta == 0 catches a seller-make-whole-on-innocent
        // double-spend independently of the offender delta.
        uint256 offenderBefore = offender.balance;
        uint256 sellerBefore = seller.balance;
        vm.prank(arbiter);
        treasury.resolveChallenge(forfeitId, true);

        assertEq(
            offender.balance - offenderBefore,
            AMT_OFFENDER + counterBond,
            "innocent: offender escrow + counter-bond returned"
        );
        // Seller not made whole on the overturned flag: the void is unwound, no waterfall.
        assertEq(seller.balance, sellerBefore, "innocent: seller NOT made whole (void unwound, no waterfall)");
        // Forfeit + bond fully returned, nothing split out, so Treasury ends at 0 (a partial waterfall
        // split would leave a nonzero residual).
        assertEq(address(treasury).balance, 0, "innocent: forfeit + bond fully returned, no waterfall split");
        // No un-promote in v1: the promoted winner remains the high bidder.
        assertEq(auction.getLot(LOT).highBidder, cleanBidder, "lot stays promoted (no un-promote)");
    }

    function test_ResolveChallengeUpheldRunsWaterfall() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();
        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        bytes32 forfeitId = _forfeitId(offender, LOT);

        uint256 counterBond = AMT_OFFENDER;
        vm.prank(offender);
        treasury.challenge{value: counterBond}(forfeitId);

        // After the challenge Treasury holds the forfeit plus the counter-bond (2 * AMT_OFFENDER).
        assertEq(address(treasury).balance, uint256(AMT_OFFENDER) + counterBond, "Treasury holds forfeit + bond pre-resolve");

        // Innocent == false (flag upheld): the counter-bond is forfeited (not returned to the
        // offender) and the waterfall runs over the stored forfeitAmount, making the seller whole first.
        uint256 sellerBefore = seller.balance;
        uint256 offenderBefore = offender.balance;
        uint256 treasuryBefore = address(treasury).balance;
        vm.prank(arbiter);
        treasury.resolveChallenge(forfeitId, false);

        assertEq(seller.balance - sellerBefore, AMT_OFFENDER - AMT_CLEAN, "upheld: seller made whole via waterfall");
        // The offender does not recover the counter-bond on an upheld ruling (delta == 0).
        assertEq(offender.balance, offenderBefore, "upheld: offender does NOT recover the counter-bond");
        // The entire stored forfeitAmount leaves Treasury via the waterfall; the bond is
        // also forfeited, so Treasury drops by at least the forfeit. The bond's exact split is
        // governance config, so only the forfeit conservation is pinned; with offender-delta == 0
        // above, the bond cannot round-trip back to the offender.
        assertLe(address(treasury).balance, treasuryBefore - uint256(AMT_OFFENDER), "upheld: entire forfeit disbursed via waterfall");
    }

    // Distinct-paddle heap dedup. _maybeInsertIntoHeap pre-scans for the same paddleId and updates
    // in place (keeping the higher amount), so one paddle holds at most one of the five slots and
    // cannot crowd out clean bidders.
    function testFuzz_HeapDistinctPaddleDedup(uint128 a, uint128 b) external {
        // Two same-paddle bids, strictly increasing and affordable.
        a = uint128(bound(a, RESERVE_PRICE, 50 ether));
        // b must clear the 2% min-increment over a or the self-raise reverts BidTooLow. Floor at
        // a + a*2% + 1 (a <= 50 ether keeps the floor < 60 ether).
        b = uint128(bound(b, uint256(a) + (uint256(a) * MIN_INCREMENT_BPS) / 10_000 + 1, 60 ether));

        _initNative();
        _openLot();
        _mockPaddle(bidder1, PADDLE_OFFENDER);
        _depositNative(bidder1, BIG_DEPOSIT);

        // One paddle bids twice (a then a strictly-higher b); the heap must hold one slot for it at
        // the higher amount b, never two. Same principal, so the keyed nonce (bidIndex) sequences
        // 0 then 1; the self-raise's observedPrevTop is the standing top (a), so the stale-prev-top
        // guard passes.
        _placeBidNative(bidder1, 0, a, PADDLE_OFFENDER, 0);
        _placeBidNative(bidder1, 1, b, PADDLE_OFFENDER, a);
        _hammerLot();
        _mockFlagsHappy();

        // Only one distinct paddle in the heap, so no clean candidate exists below it: a promotion
        // naming slot 1 is NotPromotable (slot 1 empty, the paddle kept a single slot).
        NextCleanCandidate memory cand = _candidate(1, address(0), 0, 0, 0);
        vm.expectRevert(ISessionAuction.NotPromotable.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
    }

    // Dedup raise-in-place keeps the HIGHER amount. When a same-paddle re-bid exceeds the slot it
    // already holds, _maybeInsertIntoHeap overwrites that slot with the higher entry. After the same
    // paddle bids a then a strictly higher b, the lot's hot slot (the heap top) carries b and
    // PADDLE_OFFENDER: the single retained slot was raised, not left at a and not duplicated.
    function test_HeapDedupRaisesInPlaceKeepsHigherAmount() external {
        uint128 a = AMT_C5;                 // first (lower) same-paddle bid
        uint128 b = AMT_OFFENDER;           // strictly higher re-bid by the same paddle

        _initNative();
        _openLot();
        _mockPaddle(bidder1, PADDLE_OFFENDER);
        _depositNative(bidder1, BIG_DEPOSIT);

        // Same paddle, two ascending bids; _maybeInsertIntoHeap raises the one slot to b in place.
        // Same principal, so the keyed nonce (bidIndex) sequences 0 then 1; the self-raise's
        // observedPrevTop is the standing top (a).
        _placeBidNative(bidder1, 0, a, PADDLE_OFFENDER, 0);
        _placeBidNative(bidder1, 1, b, PADDLE_OFFENDER, a);
        _hammerLot();

        // The retained slot (mirrored to the hot slot for the single distinct paddle) holds b at
        // PADDLE_OFFENDER, never the stale a.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.highBid, b, "dedup raised the surviving slot to the higher amount b");
        assertEq(lot.paddleId, PADDLE_OFFENDER, "surviving slot keeps the same paddle");

        // No duplicate slot exists for that paddle: slot 1 is empty, so a promotion naming it is
        // NotPromotable (the single-slot half of the dedup, alongside the raise-in-place value above).
        _mockFlagsHappy();
        NextCleanCandidate memory dup = _candidate(1, address(0), 0, 0, 0);
        vm.expectRevert(ISessionAuction.NotPromotable.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), dup);
    }

    // Heap eviction releases only that bidder's escrow (no double-lock). In steady state only
    // lot.highBidder has nonzero committed; an outbid bidder has committed == 0 with its slack
    // remaining as free (kept solvent for a possible promotion).
    function test_HeapEvictionReleasesOnlyThatBidder() external {
        _initNative();
        _openLot();
        _mockPaddle(offender, PADDLE_OFFENDER);
        _mockPaddle(cleanBidder, PADDLE_CLEAN);
        _depositNative(offender, BIG_DEPOSIT);
        _depositNative(cleanBidder, BIG_DEPOSIT);

        // cleanBidder bids first (top, committed == AMT_CLEAN), then offender outbids them, releasing
        // cleanBidder's committed back to free (committed == 0). Two distinct principals, so each
        // starts its keyed nonce at bidIndex 0; observedPrevTop sequences 0 then AMT_CLEAN.
        _placeBidNative(cleanBidder, 0, AMT_CLEAN, PADDLE_CLEAN, 0);
        _placeBidNative(offender, 0, AMT_OFFENDER, PADDLE_OFFENDER, AMT_CLEAN);

        // The previous top's entire committed returned to free (no double-lock), so free == deposit;
        // the current top's free is reduced by its committed bid.
        assertEq(auction.withdrawableFree(LOT, cleanBidder), BIG_DEPOSIT, "outbid bidder fully released to free");
        assertEq(
            auction.withdrawableFree(LOT, offender),
            BIG_DEPOSIT - AMT_OFFENDER,
            "current top free reduced by committed bid"
        );
    }

    // Flag-on-principal, never the executor. The flag check keys on paddleOf(principal) ==
    // lot.highBidder, never the executor/msg.sender, so an agent template cannot be mass-flagged.
    function test_FlagKeysOnPrincipalNotExecutor() external {
        _initNative();
        _openLot();
        _mockPaddle(cleanBidder, PADDLE_CLEAN);
        _mockPaddle(offender, PADDLE_OFFENDER);
        _depositNative(cleanBidder, BIG_DEPOSIT);
        _depositNative(offender, BIG_DEPOSIT);

        // cleanBidder self-bids (slot 0). The offender's top bid is submitted by `relayer` (the
        // executor) but signature-bound to `offender` (the principal): lot.highBidder is the
        // principal, never the executor. Each is its principal's first bid, so bidIndex == 0.
        _placeBidNative(cleanBidder, 0, AMT_CLEAN, PADDLE_CLEAN, 0);
        _placeBidFromRelayerNative(offender, 0, AMT_OFFENDER, PADDLE_OFFENDER, AMT_CLEAN);
        _hammerLot();

        assertEq(auction.getLot(LOT).highBidder, offender, "highBidder = principal, not executor");

        // Flag membership is checked against the principal's paddle (PADDLE_OFFENDER ==
        // paddleOf(offender)), never the executor's; the promoted candidate is cleanBidder at slot 0.
        _mockFlagsHappy();
        vm.expectCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector, SESSION_ID, PADDLE_OFFENDER)
        );
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.LotVoided(LOT, offender, cleanBidder, AMT_CLEAN);

        NextCleanCandidate memory cand = _candidate(0, cleanBidder, AMT_CLEAN, PADDLE_CLEAN, 1);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
    }

    // Native self-funding mismatch. depositForfeit on the native rail asserts STRICT equality
    // msg.value == forfeitAmount, never `>=`: a registered clone that under-pays OR over-pays is
    // rejected with WrongDenomination. Driven as the registered clone so onlyAuction passes and the
    // value check is isolated.
    function test_RevertWhen_DepositForfeitNativeValueMismatch() external {
        // A native-rail clone (paymentToken == address(0)), registered as the caller, so onlyAuction
        // passes and depositForfeit takes the native branch.
        _initNative();
        treasury.registerClone(address(auction));
        // One wei above the forfeit so both the under-pay and over-pay pushes are self-funded.
        vm.deal(address(auction), AMT_OFFENDER + 1);

        // Under-pay by 1 wei: msg.value != forfeitAmount -> revert.
        vm.expectRevert(ISessionAuction.WrongDenomination.selector);
        vm.prank(address(auction));
        treasury.depositForfeit{value: AMT_OFFENDER - 1}(
            offender, cleanBidder, LOT, AMT_OFFENDER, AMT_OFFENDER, AMT_CLEAN, seller
        );

        // Over-pay by 1 wei: a strict `==` must reject this; a buggy `>=` would accept it and leak
        // surplus native into the forfeit accounting.
        vm.expectRevert(ISessionAuction.WrongDenomination.selector);
        vm.prank(address(auction));
        treasury.depositForfeit{value: AMT_OFFENDER + 1}(
            offender, cleanBidder, LOT, AMT_OFFENDER, AMT_OFFENDER, AMT_CLEAN, seller
        );
    }

    // ERC-20 transfer-failure. On the token rail depositForfeit pulls exactly forfeitAmount via
    // safeTransferFrom(token, clone, this) and asserts msg.value == 0. If the clone never approved
    // Treasury (allowance 0) the pull reverts; with a standard reverting OZ ERC20, SafeERC20 bubbles
    // the token's own ERC20InsufficientAllowance verbatim (SafeERC20FailedOperation is reserved for
    // non-reverting tokens that return false).
    function test_RevertWhen_DepositForfeitErc20TransferFails() external {
        // A fresh ERC-20-rail clone, registered as the depositForfeit caller.
        SessionAuction erc20Clone = SessionAuction(Clones.clone(address(impl)));
        vm.prank(address(hammer));
        erc20Clone.initialize(_defaultInitConfig(address(token)));
        treasury.registerClone(address(erc20Clone));

        // The clone holds the forfeit tokens but has NOT approved Treasury -> safeTransferFrom fails.
        token.mint(address(erc20Clone), uint256(AMT_OFFENDER_T));

        // The standard token reverts ERC20InsufficientAllowance(spender=Treasury, allowance=0, needed=amt),
        // which SafeERC20 bubbles verbatim (it does not wrap a reverting token).
        vm.expectRevert(
            abi.encodeWithSelector(
                IERC20Errors.ERC20InsufficientAllowance.selector, address(treasury), 0, uint256(AMT_OFFENDER_T)
            )
        );
        vm.prank(address(erc20Clone));
        // No msg.value on the ERC-20 rail; the pull is what fails (allowance 0).
        treasury.depositForfeit(
            offender, cleanBidder, LOT, uint256(AMT_OFFENDER_T), uint256(AMT_OFFENDER_T), uint256(AMT_CLEAN_T), seller
        );
    }

    // depositForfeit stores forfeitAmount as the disburse basis. The persisted forfeitAmount is the
    // basis a later disburse splits: the entire stored amount leaves Treasury on disburse, proving
    // forfeits[id].forfeitAmount was the split basis (not msg.value, not offenderClearing). Exercised
    // end-to-end via a real void on the native rail.
    function test_DepositForfeitStoresAmountAsBasis() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        bytes32 forfeitId = _forfeitId(offender, LOT);

        // Treasury now holds exactly the stored forfeitAmount (AMT_OFFENDER) and nothing else.
        assertEq(address(treasury).balance, AMT_OFFENDER, "Treasury holds the stored forfeitAmount");

        // After the window, disburse splits THAT stored amount: the whole AMT_OFFENDER leaves.
        vm.warp(block.timestamp + 30 days);
        treasury.disburse(forfeitId);

        assertEq(address(treasury).balance, 0, "disburse splits the stored forfeitAmount in full");
    }

    // Insufficient counter-bond. challenge(forfeitId) requires
    // bond >= forfeitAmount*counterBondBps/1e4 (against the stored forfeitAmount). An under-bond is
    // rejected with WrongBond and the forfeit stays unchallenged, so a later disburse is NOT blocked.
    function test_RevertWhen_ChallengeBondTooLow() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        bytes32 forfeitId = _forfeitId(offender, LOT);

        // A 0-wei bond is below any positive counterBondBps threshold against forfeitAmount.
        vm.expectRevert(ISessionAuction.WrongBond.selector);
        vm.prank(offender);
        treasury.challenge{value: 0}(forfeitId);

        // The under-bonded challenge did NOT take: disburse remains runnable (not blocked).
        vm.warp(block.timestamp + 30 days);
        treasury.disburse(forfeitId);

        assertEq(address(treasury).balance, 0, "unchallenged forfeit still disburses after a failed under-bond");
    }

    // Rebate-cap branch. The waterfall rebate is min(remainder*bps/1e4, cap); the cap bounds the
    // false-flag payoff. At a high value tier (remainder*bps/1e4 > cap) the cap binds. ITreasury has
    // no cap getter, so this asserts the consequence (rebate strictly below the uncapped value) plus
    // full conservation, without pinning the exact cap.
    function test_DisburseRebateCapBinds() external {
        // High-value tier: a large clearing price so remainder*disruptionRebateBps/1e4 exceeds any
        // sane disruptionRebateCap, forcing the cap to bind.
        uint128 bigOffender = 100_000 ether;
        uint128 bigClean = 80_000 ether;
        SessionAuction a = _hammeredRingNativeAt(bigOffender, bigClean);
        _mockFlagsHappy();

        NextCleanCandidate memory cand = _cleanCandidateAt(4, bigClean);
        vm.prank(relayer);
        a.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        bytes32 forfeitId = _forfeitId2(address(a), offender, LOT);

        vm.warp(block.timestamp + 30 days);
        uint256 promotedBefore = cleanBidder.balance;
        uint256 treasuryBefore = address(treasury).balance;

        treasury.disburse(forfeitId);

        // Uncapped rebate at this tier (default disruptionRebateBps = 100): an uncapped waterfall would
        // pay exactly this, so paidRebate < uncappedRebate can only happen if the cap clipped it.
        uint256 makeWhole = uint256(bigOffender) - bigClean;
        uint256 remainder = uint256(bigOffender) - makeWhole;
        uint256 uncappedRebate = (remainder * DISRUPTION_REBATE_BPS) / 1e4; // == 800 ether here

        // The cap binds: the promoted winner receives strictly less than the uncapped rebate (the
        // difference goes to the neutral sink).
        uint256 paidRebate = cleanBidder.balance - promotedBefore;
        assertLt(paidRebate, uncappedRebate, "cap binds: rebate strictly below the uncapped arm");

        // Conservation across the capped split: the entire forfeit still leaves Treasury.
        assertEq(address(treasury).balance, treasuryBefore - uint256(bigOffender), "capped split conserves the forfeit");
    }

    // False-flag-for-profit is net-negative ACROSS VALUE TIERS. Fuzzed over
    // (offenderClearing, promotedPrice) pairs (promoted strictly below offender) spanning low to high
    // tiers (including the cap-binding region). The colluding friend pays their own promoted bid and
    // grosses at most the (capped) rebate, so the attacker is net-negative.
    function testFuzz_FalseFlagNetNegativeAcrossTiers(uint128 offenderClearing, uint128 promotedPrice) external {
        // Bound to a strictly-descending, affordable pair. promotedPrice floored at 5 ether so the
        // lower heap ladder (cleanAmt/5..) stays >= RESERVE_PRICE; the offender floor is promotedPrice
        // + 2% min-increment + 1 ether (a flat +1 ether fails BidTooLow at high tiers). The 50_000
        // ether ceiling keeps that floor under the 100_000 ether top while still spanning the
        // cap-binding tier.
        promotedPrice = uint128(bound(promotedPrice, 5 ether, 50_000 ether));
        uint256 offenderFloor = uint256(promotedPrice) + (uint256(promotedPrice) * MIN_INCREMENT_BPS) / 10_000 + 1 ether;
        offenderClearing = uint128(bound(offenderClearing, offenderFloor, 100_000 ether));

        SessionAuction a = _hammeredRingNativeAt(offenderClearing, promotedPrice);
        _mockFlagsHappy();

        uint256 friendFreeBefore = a.withdrawableFree(LOT, cleanBidder);

        NextCleanCandidate memory cand = _cleanCandidateAt(4, promotedPrice);
        vm.prank(relayer);
        a.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        bytes32 forfeitId = _forfeitId2(address(a), offender, LOT);

        // The friend PAID their own promoted bid (no windfall, no free lot).
        assertEq(
            friendFreeBefore - a.withdrawableFree(LOT, cleanBidder),
            promotedPrice,
            "friend paid own bid across tiers"
        );

        vm.warp(block.timestamp + 30 days);
        uint256 friendBefore = cleanBidder.balance;
        treasury.disburse(forfeitId);
        uint256 friendGross = cleanBidder.balance - friendBefore;

        // Net-negative: the friend's gross rebate is strictly less than the bid they had to pay,
        // at EVERY tier (the rebate is a small fraction of the remainder and is cap-bounded above).
        assertLt(friendGross, promotedPrice, "attacker net-negative: gross rebate < bid paid (all tiers)");
    }

    // voidAndAward reentrancy guard. voidAndAward is nonReentrant. The void's single cross-contract
    // call is depositForfeit; a hostile Treasury that re-enters voidAndAward during it is rejected by
    // the guard (ReentrancyGuardTransient).
    function test_RevertWhen_VoidReentered() external {
        // Build the ring on a clone wired to a reentrant treasury (so depositForfeit re-enters).
        D_ReentrantTreasury evil = new D_ReentrantTreasury();
        SessionAuction a = _hammeredRingWithTreasury(address(evil));
        _mockFlagsHappy();
        evil.arm(a, LOT, _flaggedProof(PADDLE_OFFENDER), _cleanCandidate(4));

        NextCleanCandidate memory cand = _cleanCandidate(4);

        // The outer void calls depositForfeit -> evil re-enters voidAndAward -> guard trips.
        vm.expectRevert(ReentrancyGuardTransient.ReentrancyGuardReentrantCall.selector);
        vm.prank(relayer);
        a.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
    }

    // Post-void reveal re-bind. voidAndAward re-binds lot.winnerSeq = candidate.seq, which gates the
    // reveal: a reveal at the promoted winner's new seq is the canonical target, while a reveal at the
    // forfeited offender's stale seq reverts WrongSeq.
    function test_RevertWhen_RevealStaleOffenderSeqAfterVoid() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        uint64 offenderSeq = 5; // offender is the 5th ascending bid (_bidSeq == 5)
        uint64 candidateSeq = 4; // promoted candidate is the 4th

        NextCleanCandidate memory cand = _cleanCandidate(candidateSeq);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // The void re-bound winnerSeq to the promoted candidate.seq (asserted directly).
        assertEq(auction.getLot(LOT).winnerSeq, candidateSeq, "winnerSeq re-bound to promoted seq");

        // A reveal at the OFFENDER's stale seq is no longer the winning seq -> WrongSeq.
        vm.prank(cleanBidder);
        vm.expectRevert(ISessionAuction.WrongSeq.selector);
        auction.reveal(LOT, offenderSeq, uint128(BIG_DEPOSIT), bytes32("salt"));
    }

    // Full-heap crowd-out resistance. Five distinct paddles fill all five slots, then one re-bids
    // higher. Dedup raises that paddle in place (still one slot), so a clean lower bidder is not
    // evicted by a duplicate and stays promotable.
    function test_FullHeapRebidKeepsOneSlot() external {
        // Build the ring WITHOUT hammering so the offender's re-bid lands while still Open (a re-bid
        // after hammer would revert NotOpen); _hammerLot() below seals it.
        _buildOpenRingNative(); // 5 distinct paddles fill all slots, offender top

        // The offender re-bids higher; dedup must keep it in one slot and not evict cleanBidder.
        // This is the offender's second bid, so its keyed nonce bidIndex is 1.
        _placeBidNative(offender, 1, AMT_OFFENDER + 10 ether, PADDLE_OFFENDER, AMT_OFFENDER);
        _hammerLot();
        _mockFlagsHappy();

        // The offender still holds one slot at the raised amount, so promoting the unchanged clean
        // candidate (cleanBidder, slot 3) succeeds. A duplicate offender slot would have crowded out
        // cleanBidder, making this BadCandidate (mismatch) or NotPromotable (empty).
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.LotVoided(LOT, offender, cleanBidder, AMT_CLEAN);

        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        assertEq(auction.getLot(LOT).highBidder, cleanBidder, "clean lower bidder not evicted by a duplicate");
    }

    // Over-deposit fund safety. Over-depositing is never penalized. The offender funded BIG_DEPOSIT
    // but bid only AMT_OFFENDER, so the slack stayed `free` while the bid moved
    // free->committed->escrowAmount at hammer. _captureForfeit forfeits only the clearing-price
    // escrow, never the slack: the offender's free stays withdrawable and the clone balance falls by
    // exactly the clearing price. A capture that grabbed the whole deposit would pass every expectCall
    // (which pins only forfeitAmount) but is caught here by the residual free.
    function test_OffenderKeepsSlackOnlyClearingPriceForfeited() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        // Pre-void: offender bid 100e of a 200e deposit, so 100e of slack stayed `free`; the bid's
        // 100e is in escrowAmount (hammer moved committed -> escrowAmount).
        assertEq(auction.withdrawableFree(LOT, offender), BIG_DEPOSIT - AMT_OFFENDER, "offender slack pre-void");
        assertEq(auction.getLot(LOT).escrowAmount, AMT_OFFENDER, "offender escrow = clearing price pre-void");

        uint256 cloneBefore = address(auction).balance;

        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // Only the clearing-price escrow was forfeited: the offender's unlocked slack is untouched
        // and still withdrawable.
        assertEq(
            auction.withdrawableFree(LOT, offender),
            BIG_DEPOSIT - AMT_OFFENDER,
            "offender keeps the full slack (only clearing-price escrow forfeited)"
        );

        // The clone balance fell by exactly the clearing price (the single transfer out), so the
        // slack was not swept into the forfeit alongside the escrow.
        assertEq(
            cloneBefore - address(auction).balance,
            AMT_OFFENDER,
            "clone falls by exactly the clearing price, not the whole deposit"
        );

        // The offender can actually pull that slack back out (genuinely free): the withdraw lands
        // and leaves 0 free.
        uint256 walletBefore = offender.balance;
        vm.prank(offender);
        auction.withdrawDeposit(LOT, BIG_DEPOSIT - AMT_OFFENDER);

        assertEq(offender.balance - walletBefore, BIG_DEPOSIT - AMT_OFFENDER, "offender withdraws the unpenalized slack");
        assertEq(auction.withdrawableFree(LOT, offender), 0, "offender free fully drained after slack withdraw");
    }

    // All-flagged ring of five (escalation trigger). Five distinct flagged paddles fill all five
    // slots, so a well-formed (non-empty, field-matching) candidate exists but every slot is flagged.
    // With a full heap there is no empty slot, so the revert is BadCandidate (the candidate's own
    // non-membership proof fails), never NotPromotable (the empty-slot guard). No clean slot is
    // promotable, so the lot stays Hammered and the operator must escalate to voidSession. Two
    // distinct filled slots are rejected to prove no slot in the ring is promotable.
    function test_RevertWhen_RingOfFiveNoCleanCandidate() external {
        _buildHammeredRingNative(); // 5 distinct paddles, all slots filled, offender top

        uint256 treasuryBefore = address(treasury).balance; // no forfeit may be routed on revert

        // Every paddle is flagged (membership true, non-membership false), so no candidate in the
        // full heap can satisfy the required positive non-membership proof.
        vm.mockCall(address(flags), abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector), abi.encode(true));
        vm.mockCall(address(flags), abi.encodeWithSelector(IFlagRegistry.verifyNonMembership.selector), abi.encode(false));

        // (a) the highest clean-looking slot (cleanBidder, idx 3) is non-empty and field-matching,
        //     yet flagged -> BadCandidate (not NotPromotable: the slot is filled).
        NextCleanCandidate memory top = _cleanCandidate(4);
        vm.expectRevert(ISessionAuction.BadCandidate.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), top);

        // (b) a different non-empty slot (ringB3, idx 2) is equally unpromotable: also BadCandidate.
        NextCleanCandidate memory mid = _candidate(2, ringB3, AMT_C3, PADDLE_C3, 3);
        vm.expectRevert(ISessionAuction.BadCandidate.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), mid);

        // Lot unchanged (still Hammered, offender still winner, escrow intact), no forfeit routed by
        // either attempt; the only escape is voidSession.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Hammered), "all-flagged ring stays Hammered (forces voidSession)");
        assertEq(lot.highBidder, offender, "offender still winner after both rejections");
        assertEq(lot.escrowAmount, AMT_OFFENDER, "offender escrow untouched after both rejections");
        assertEq(address(treasury).balance, treasuryBefore, "no forfeit routed when no clean candidate exists");
    }

    // Double-void / replay. After a successful voidAndAward the lot is Voided; a second voidAndAward
    // hits the phase guard and reverts NotHammered (the NotHammered path from the Voided state, as
    // opposed to from a never-hammered Open lot). Nothing may move on the replay (no second forfeit,
    // no re-promote).
    function test_RevertWhen_VoidTwice() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        // First void succeeds: lot -> Voided, promoted winner = cleanBidder, escrow = AMT_CLEAN.
        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        assertEq(auction.getLot(LOT).phase, uint8(LotPhase.Voided), "first void promoted to Voided");

        // Snapshot the post-first-void state and Treasury balance; the replay must not move them.
        uint256 escrowAfterFirst = auction.getLot(LOT).escrowAmount;
        address bidderAfterFirst = auction.getLot(LOT).highBidder;
        uint256 treasuryAfterFirst = address(treasury).balance;

        // Second void on the SAME (now Voided) lot: phase != Hammered -> NotHammered (phase guard).
        NextCleanCandidate memory cand2 = _cleanCandidate(4);
        vm.expectRevert(ISessionAuction.NotHammered.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand2);

        // No second forfeit routed, no re-promotion: the lot and Treasury are exactly as the first
        // void left them (a partial-mutation-before-revert or double-forfeit bug is caught here).
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Voided), "stays Voided after the rejected replay");
        assertEq(lot.escrowAmount, escrowAfterFirst, "escrowAmount unchanged by the rejected replay");
        assertEq(lot.highBidder, bidderAfterFirst, "highBidder unchanged by the rejected replay");
        assertEq(address(treasury).balance, treasuryAfterFirst, "no second forfeit routed on the replay");
    }

    // Disjoint disputes. An open Treasury forfeit challenge does not block the promoted winner's
    // delivery: with forfeits[id].challenged == true, the lot escrow is untouched and the lot still
    // advances Voided -> Awaiting via finalizeWinner. The forfeit challenge freezes only the
    // offender's Treasury escrow, never the SessionAuction lot escrow.
    function test_OpenForfeitChallengeDoesNotBlockPromotedWinnerDelivery() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        // Void + promote: lot -> Voided, promoted winner cleanBidder, escrow = AMT_CLEAN.
        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        bytes32 forfeitId = _forfeitId(offender, LOT);

        uint40 voidedAt = auction.getLot(LOT).voidedAt;

        // The offender opens a forfeit challenge (challenged = true), freezing only the offender's
        // forfeited Treasury escrow.
        vm.prank(offender);
        treasury.challenge{value: AMT_OFFENDER}(forfeitId);

        // The promoted winner's lot escrow is untouched by the open challenge (no shared flag).
        assertEq(auction.getLot(LOT).escrowAmount, AMT_CLEAN, "promoted escrow untouched by the open forfeit challenge");

        // With the challenge still open, the lot finalizes Voided -> Awaiting once the AC window
        // closes. Warp past the window and any reveal deadline so the finalize gate is met.
        vm.warp(uint256(voidedAt) + 30 days);

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.WinnerFinalized(LOT, cleanBidder, AMT_CLEAN);
        auction.finalizeWinner(LOT);

        // The promoted winner reached AwaitingDelivery with the forfeit challenge still open: the two
        // disputes and their funds are disjoint.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Awaiting), "promoted winner finalized to Awaiting despite open forfeit challenge");
        assertEq(lot.deliveryState, uint8(DeliveryState.AwaitingDelivery), "deliveryState = AwaitingDelivery");
        assertEq(lot.awaitingAt, uint40(block.timestamp), "awaitingAt set at finalize");
        assertEq(lot.escrowAmount, AMT_CLEAN, "promoted escrow carried into delivery unchanged");
    }

    // Treasury.disburse is single-shot. disburse is permissionless, so a second disburse of the same
    // forfeitId would re-run the waterfall and drain Treasury again (from another forfeit's or the
    // contract's own funds). The record must be consumed on the first disburse. ITreasury declares no
    // errors, so the second disburse expects NothingToWithdraw (from ISessionAuction); the conservation
    // backstop (Treasury does not drop again) is the load-bearing check.
    function test_RevertWhen_DisburseTwice() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();
        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        bytes32 forfeitId = _forfeitId(offender, LOT);

        // First disburse (after the window, unchallenged): drops Treasury by exactly the forfeit.
        vm.warp(block.timestamp + 30 days);
        uint256 treasuryBeforeFirst = address(treasury).balance;
        treasury.disburse(forfeitId);

        uint256 treasuryAfterFirst = address(treasury).balance;
        assertEq(treasuryBeforeFirst - treasuryAfterFirst, AMT_OFFENDER, "first disburse pays out exactly the forfeit");

        // Second disburse of the same id: the record was consumed, so it reverts and pays nothing.
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        treasury.disburse(forfeitId);

        // Conservation backstop: Treasury did not drop a second time (catches a re-run waterfall even
        // if the selector guess is off).
        assertEq(address(treasury).balance, treasuryAfterFirst, "no second payout on the re-disburse");
    }

    // disburse AFTER resolveChallenge consumes the same record. resolveChallenge is the other terminal
    // of a forfeit: on innocent == true it returns escrow + bond and consumes the record, so a
    // follow-up disburse(forfeitId) must revert and move no further funds (else a forfeit already paid
    // back to an innocent offender could be disbursed). Expects NothingToWithdraw (from ISessionAuction)
    // as in test_RevertWhen_DisburseTwice; the conservation backstop is the load-bearing check.
    function test_RevertWhen_DisburseAfterResolveChallenge() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        bytes32 forfeitId = _forfeitId(offender, LOT);

        // Offender challenges (sufficient bond), arbiter rules INNOCENT: escrow + bond returned and the
        // forfeit record is consumed. After this, Treasury holds neither the forfeit nor the bond for
        // this id.
        uint256 counterBond = AMT_OFFENDER;
        vm.prank(offender);
        treasury.challenge{value: counterBond}(forfeitId);
        vm.prank(arbiter);
        treasury.resolveChallenge(forfeitId, true);

        uint256 treasuryAfterResolve = address(treasury).balance;

        // A disburse on the already-resolved id must revert (record consumed) and move no funds.
        vm.warp(block.timestamp + 30 days);
        vm.expectRevert(ISessionAuction.NothingToWithdraw.selector);
        treasury.disburse(forfeitId);

        // CONSERVATION backstop: no further funds leave Treasury on the post-resolve disburse.
        assertEq(address(treasury).balance, treasuryAfterResolve, "no payout disbursing an already-resolved forfeit");
    }

    // disburse is gated on the challenge window, which protects the offender's right to challenge.
    // Skipping the gate would let anyone disburse the instant the void lands, denying the offender any
    // chance to challenge. The exact off-by-one second cannot be pinned (forfeitChallengeSec is
    // Treasury governance config), so this asserts the immediate-after-void rejection. Expects
    // AcWindowOpen (from ISessionAuction); the conservation backstop (no waterfall ran) is the
    // load-bearing check.
    function test_RevertWhen_DisburseBeforeChallengeWindow() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);
        bytes32 forfeitId = _forfeitId(offender, LOT);

        // Treasury holds the freshly-deposited forfeit and nothing has been disbursed.
        uint256 treasuryBefore = address(treasury).balance;
        assertEq(treasuryBefore, AMT_OFFENDER, "Treasury holds the undisbursed forfeit immediately after the void");

        // WITHOUT warping past forfeitChallengeSec: disbursing now must be rejected (the offender's
        // challenge window is still open).
        vm.expectRevert(ISessionAuction.AcWindowOpen.selector);
        treasury.disburse(forfeitId);

        // CONSERVATION backstop: no waterfall ran, so the forfeit is untouched and the offender's
        // right to challenge is preserved.
        assertEq(address(treasury).balance, treasuryBefore, "no waterfall before the challenge window closes");
    }

    // Offender membership-replay. Twin of test_RevertWhen_NonMembershipProofReplayed: a
    // verifyMembership proof valid for a different paddle is not replayable for lot.paddleId. The
    // membership check keys on lot.paddleId (the winner's paddle), so a proof valid for PADDLE_CLEAN
    // does not verify for PADDLE_OFFENDER -> NotFlagged.
    function test_RevertWhen_OffenderMembershipProofReplayed() external {
        _buildHammeredRingNative();
        NextCleanCandidate memory cand = _cleanCandidate(4);

        // A membership proof valid for PADDLE_CLEAN (a DIFFERENT paddle) is supplied as the offender's
        // flag-inclusion proof. The registry pins low == p to the CLAIMED paddle, so the proof
        // verifies for PADDLE_CLEAN but NOT for the winner's actual paddle (PADDLE_OFFENDER).
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector, SESSION_ID, PADDLE_CLEAN),
            abi.encode(true)
        );
        // verifyMembership for the ACTUAL winner paddle (lot.paddleId == PADDLE_OFFENDER) is false:
        // the replayed wrong-paddle proof cannot satisfy the keyed-on-lot.paddleId membership check.
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector, SESSION_ID, PADDLE_OFFENDER),
            abi.encode(false)
        );

        vm.expectRevert(ISessionAuction.NotFlagged.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_CLEAN), cand);

        // No side effect: lot untouched (still Hammered, offender still winner, escrow intact).
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Hammered), "stays Hammered after the replayed-proof NotFlagged");
        assertEq(lot.highBidder, offender, "offender still highBidder after the replayed-proof NotFlagged");
        assertEq(lot.escrowAmount, AMT_OFFENDER, "offender escrow untouched after the replayed-proof NotFlagged");
    }

    // _relockPromoted solvency boundary, EXACT. The promoted candidate must have free >=
    // promotedAmount. Free is withdrawn to exactly the bid (free == AMT_CLEAN): the relock must
    // succeed, draining free to 0 and locking escrow at AMT_CLEAN. An impl using `free > amount` would
    // reject this. Off-by-one twin: test_RevertWhen_PromotedFreeOneWeiShort.
    function test_PromotedFreeExactlyEqualsBidSucceeds() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        // Withdraw the slack so the promoted candidate's free is EXACTLY their bid (AMT_CLEAN).
        vm.prank(cleanBidder);
        auction.withdrawDeposit(LOT, BIG_DEPOSIT - AMT_CLEAN);
        assertEq(auction.withdrawableFree(LOT, cleanBidder), AMT_CLEAN, "free withdrawn to exactly the bid");

        NextCleanCandidate memory cand = _cleanCandidate(4);

        // free == amount satisfies the >= gate: the void promotes and re-locks the full free.
        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.LotVoided(LOT, offender, cleanBidder, AMT_CLEAN);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Voided), "phase Voided on the exact-boundary promotion");
        assertEq(lot.highBidder, cleanBidder, "highBidder = promoted on the exact boundary");
        assertEq(lot.escrowAmount, AMT_CLEAN, "escrow = promoted bid on the exact boundary");

        // The relock drained the candidate's entire free (free == amount, so 0 remains).
        assertEq(auction.withdrawableFree(LOT, cleanBidder), 0, "free fully relocked into committed/escrow");
    }

    // _relockPromoted solvency boundary OFF-BY-ONE (twin of test_PromotedFreeExactlyEqualsBidSucceeds).
    // free withdrawn to one wei below the bid (free == AMT_CLEAN - 1): the relock reverts
    // InsufficientFreeBalance and the whole tx unwinds. Together with the sibling, this pins the
    // boundary at >= precisely.
    function test_RevertWhen_PromotedFreeOneWeiShort() external {
        _buildHammeredRingNative();
        _mockFlagsHappy();

        // One wei short: free == AMT_CLEAN - 1 < the bid, so the relock cannot lock the full amount.
        vm.prank(cleanBidder);
        auction.withdrawDeposit(LOT, BIG_DEPOSIT - AMT_CLEAN + 1);
        assertEq(auction.withdrawableFree(LOT, cleanBidder), AMT_CLEAN - 1, "free one wei below the bid");

        uint256 treasuryBefore = address(treasury).balance; // the forfeit must NOT route on revert

        NextCleanCandidate memory cand = _cleanCandidate(4);
        vm.expectRevert(ISessionAuction.InsufficientFreeBalance.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_OFFENDER), cand);

        // The whole void unwound: lot still Hammered, offender escrow intact, no forfeit routed.
        Lot memory lot = auction.getLot(LOT);
        assertEq(lot.phase, uint8(LotPhase.Hammered), "stays Hammered when the relock is one wei short");
        assertEq(lot.highBidder, offender, "offender still winner when the relock reverts");
        assertEq(lot.escrowAmount, AMT_OFFENDER, "offender escrow untouched when the relock reverts");
        assertEq(address(treasury).balance, treasuryBefore, "no forfeit routed when the relock reverts");
    }

    // Heap MIN-REPLACE eviction. When the heap is full and an incoming entry's amount exceeds the
    // lowest occupant's, that minimum slot is overwritten. A 6th distinct paddle bidding above the
    // heap minimum (placeBid accepts only a strict new top) must evict the lowest occupant (ringB5 @
    // AMT_C5, slot 0) and take its slot.
    // Part A (negative): the evicted bidder's old slot no longer matches its fields -> BadCandidate.
    // Part B (positive): the slot now holds the 6th bidder, proven by promoting a surviving lower
    // clean slot that requires the 6th's paddle to be proven-flagged-above (precedingFlagInclusion).
    function test_HeapMinReplaceEvictsLowestDistinctPaddle() external {
        // Part A: the 6th distinct paddle (PADDLE_C6) bids above the offender, becoming the new top
        // and evicting the lowest heap occupant (ringB5 @ AMT_C5, slot 0).
        address sixth = _buildHammeredRing6On(auction, AMT_OFFENDER + 20 ether);

        // Reaching the candidate field-match check needs only the winner (PADDLE_C6) to prove flagged.
        vm.mockCall(address(flags), abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector), abi.encode(true));

        // The evicted ringB5's fields no longer match its old slot 0 (now the 6th bidder) -> BadCandidate.
        NextCleanCandidate memory evicted = _candidate(0, ringB5, AMT_C5, PADDLE_C5, 1);

        vm.expectRevert(ISessionAuction.BadCandidate.selector);
        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_C6), evicted);

        // The 6th distinct paddle is the new top; the eviction itself is proven positively in Part B.
        assertEq(auction.getLot(LOT).highBidder, sixth, "6th distinct paddle is the new top after its bid");
        assertEq(auction.getLot(LOT).paddleId, PADDLE_C6, "top paddle = the 6th distinct paddle");

        // Part B (fresh clone, same topology): the 6th occupies the evicted slot. Promote the
        // surviving original offender (slot 4), the highest unflagged below the 6th, so the only
        // strictly-higher slot (the 6th @ slot 0) must be proven flagged. Success proves slot 0 holds
        // the 6th and the original offender slot survived the min-replace intact.
        SessionAuction a = SessionAuction(Clones.clone(address(impl)));
        _buildHammeredRing6On(a, AMT_OFFENDER + 20 ether);

        // winner (6th) flagged; the promoted candidate (original offender paddle) clean.
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector, SESSION_ID, PADDLE_C6),
            abi.encode(true)
        );
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyNonMembership.selector, SESSION_ID, PADDLE_OFFENDER),
            abi.encode(true)
        );

        // heapIndex 4 holds the original offender; the one strictly-higher slot is the 6th (PADDLE_C6),
        // supplied as the single preceding-flag-inclusion proof.
        NextCleanCandidate memory promoteSurvivor = _candidate(4, offender, AMT_OFFENDER, PADDLE_OFFENDER, 5);

        vm.expectEmit(true, true, true, true, address(a));
        emit ISessionAuction.LotVoided(LOT, sixth, offender, AMT_OFFENDER);

        vm.prank(relayer);
        a.voidAndAward(LOT, _flaggedProof(PADDLE_C6), promoteSurvivor);

        assertEq(a.getLot(LOT).highBidder, offender, "surviving slot promoted: 6th occupied slot 0, evicting only the min");
        assertEq(a.getLot(LOT).escrowAmount, AMT_OFFENDER, "promoted survivor escrow = its own bid");
    }

    // Heap MIN-REPLACE keeps the higher slots intact (the `> min` boundary). placeBid admits only a
    // strict new top, so a full-heap 6th bid is always the new MAX and always above the heap minimum;
    // it must displace only the minimum slot and leave non-minimum slots intact. After the 6th bid
    // evicts only ringB5 (the min), a surviving higher clean slot (cleanBidder @ slot 3) is still a
    // valid promotable candidate.
    function test_HeapMinReplaceKeepsHigherSlotsIntact() external {
        _buildHammeredRing6On(auction, AMT_OFFENDER + 20 ether); // 6th evicts only the min (ringB5)
        _mockFlagsHappy(); // offender + 6th flagged-by-default; cleanBidder clean (non-membership true)

        // The 6th (winner) paddle must also prove flagged (it is the top, above cleanBidder).
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector, SESSION_ID, PADDLE_C6),
            abi.encode(true)
        );

        // cleanBidder (slot 3) survived the min-replace. The two strictly-higher slots (offender @
        // slot 4 and the 6th @ slot 0) are both flagged, so cleanBidder is the canonical next-clean
        // and promotes. A min-scan that wrongly evicted slot 3 would make this BadCandidate or
        // NotPromotable.
        NextCleanCandidate memory survivor = _candidate(3, cleanBidder, AMT_CLEAN, PADDLE_CLEAN, 4);

        vm.expectEmit(true, true, true, true, address(auction));
        emit ISessionAuction.LotVoided(LOT, ringB6, cleanBidder, AMT_CLEAN);

        vm.prank(relayer);
        auction.voidAndAward(LOT, _flaggedProof(PADDLE_C6), survivor);

        assertEq(auction.getLot(LOT).highBidder, cleanBidder, "surviving higher slot promotable: min-replace evicted only the min");
        assertEq(auction.getLot(LOT).escrowAmount, AMT_CLEAN, "promoted survivor escrow = its own bid");
    }

    // Internal helpers. They drive the real entrypoints; cross-contract stubs (paddleOf /
    // verifyMembership / verifyNonMembership) are mocked so the SessionAuction void path is isolated.

    // Session bring-up.
    function _initNative() private {
        vm.prank(address(hammer));
        auction.initialize(_defaultInitConfig(address(0)));
    }

    function _openLot() private {
        vm.prank(address(hammer));
        auction.openLot(LOT, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));
    }

    function _hammerLot() private {
        vm.warp(block.timestamp + 2 days); // past endsAt
        auction.hammer(LOT);
    }

    // Deposits.
    function _depositNative(address principal, uint256 amount) private {
        vm.prank(principal);
        auction.depositCeiling{value: amount}(LOT, amount);
    }

    function _depositToken(SessionAuction a, address principal, uint256 amount) private {
        vm.prank(principal);
        token.approve(address(a), amount);
        vm.prank(principal);
        a.depositCeiling(LOT, amount);
    }

    // Paddle and flag mocks.
    function _mockPaddle(address principal, uint16 paddleId) private {
        vm.mockCall(
            address(paddles),
            abi.encodeWithSelector(IPaddleRegistry.paddleOf.selector, principal),
            abi.encode(paddleId)
        );
    }

    // Make both flag verifiers return the happy answer: offender paddle FLAGGED (membership true)
    // and the clean candidate UNFLAGGED (non-membership true); other higher heap slots flagged.
    function _mockFlagsHappy() private {
        // Default membership true (covers the offender and the higher heap slots).
        vm.mockCall(address(flags), abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector), abi.encode(true));

        // Default non-membership true.
        vm.mockCall(address(flags), abi.encodeWithSelector(IFlagRegistry.verifyNonMembership.selector), abi.encode(true));

        // The offender paddle must NOT pass non-membership (it is flagged).
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyNonMembership.selector, SESSION_ID, PADDLE_OFFENDER),
            abi.encode(false)
        );

        // The clean candidate must NOT pass membership (it is unflagged).
        vm.mockCall(
            address(flags),
            abi.encodeWithSelector(IFlagRegistry.verifyMembership.selector, SESSION_ID, PADDLE_CLEAN),
            abi.encode(false)
        );
    }

    // Ceiling signature (real ECDSA over the clone domain).

    // The signing key bound to `principal`. placeBid recovers the ceiling sig to the `principal`
    // calldata arg, so every bidding principal must be registered (via _bindSigner); an unregistered
    // principal has key 0 and the require below fails loudly.
    function _signerKeyFor(address principal) private view returns (uint256) {
        uint256 key = _signerKey[principal];
        require(key != 0, "D: principal has no bound signing key (register it via _bindSigner)");
        return key;
    }

    function _domainSeparator(address clone) private view returns (bytes32) {
        return keccak256(abi.encode(EIP712_TYPE_HASH, HASHED_NAME, HASHED_VERSION, block.chainid, clone));
    }

    /// @dev Sign the Ceiling over the clone domain (matches SessionAuction's _hashTypedDataV4 over
    ///      CEILING_TYPEHASH). The clone's EIP-712 domain is bound to `clone`, so the digest is bound
    ///      to that exact clone address. Returns a real 65-byte (r,s,v) ECDSA sig that
    ///      SignatureChecker.isValidSignatureNowCalldata recovers to `principal` (== signer of `key`).
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

    // Envelope, quote, and signature builders. The ceiling sig is a real ECDSA over the clone domain
    // (recovers to the principal in placeBid); the attestation quote is a real low-S P256 attestation
    // by the seeded operator key.
    function _ceiling(address principal, uint64 maxBids) private view returns (Ceiling memory c) {
        c = Ceiling({
            principal: principal,
            sessionId: SESSION_ID,
            lotId: LOT,
            ceilingCommit: keccak256(abi.encode(uint128(BIG_DEPOSIT), bytes32("salt"))),
            strategy: 0,
            deadline: uint64(block.timestamp + 1 days),
            maxBids: maxBids,
            nonceKey: uint192(uint256(keccak256(abi.encode(SESSION_ID, LOT, principal))))
        });
    }

    /// @dev A real low-S P256 attestation by the seeded operator key over the 10-field digest placeBid
    ///      recomputes. The preimage binds `amount`, `bidIndex`, and the ceiling's nonceKey +
    ///      ceilingCommit, so the quote must carry the actual values or P256.verify rejects it
    ///      (BadAttestationSig).
    function _quote(Ceiling memory c, uint128 amount, uint64 bidIndex, uint128 prevTop, bytes32 nonce)
        private
        view
        returns (AttestationQuote memory q)
    {
        q = _realQuote(c, LOT, amount, bidIndex, prevTop, nonce);
    }

    function _placeBidNative(
        address principal,
        uint64 bidIndex,
        uint128 amount,
        uint16 paddleId,
        uint128 prevTop
    ) private {
        _mockPaddle(principal, paddleId);
        Ceiling memory c = _ceiling(principal, 16);
        AttestationQuote memory q = _quote(c, amount, bidIndex, prevTop, keccak256(abi.encode(principal, bidIndex)));
        bytes memory sig = _signCeiling(address(auction), c, _signerKeyFor(principal));
        vm.prank(principal);
        auction.placeBid(c, LOT, principal, bidIndex, amount, sig, _operatorKeyId(), q);
    }

    function _placeBidFromRelayerNative(
        address principal,
        uint64 bidIndex,
        uint128 amount,
        uint16 paddleId,
        uint128 prevTop
    ) private {
        _mockPaddle(principal, paddleId);
        Ceiling memory c = _ceiling(principal, 16);
        AttestationQuote memory q = _quote(c, amount, bidIndex, prevTop, keccak256(abi.encode(principal, bidIndex)));
        bytes memory sig = _signCeiling(address(auction), c, _signerKeyFor(principal));

        // Submitted by the executor (relayer) but authorized by the signature over `principal`, so
        // lot.highBidder ends up the principal, not the relayer.
        vm.prank(relayer);
        auction.placeBid(c, LOT, principal, bidIndex, amount, sig, _operatorKeyId(), q);
    }

    function _operatorKeyId() private view returns (bytes32) {
        return _baseOperatorKeyId();
    }

    // Candidate and proof builders.

    // FlagRegistry boundary-leaf proof layout: [bytes32(low), bytes32(high), siblings...].
    function _flaggedProof(uint16 paddle) private pure returns (bytes32[] memory proof) {
        proof = new bytes32[](3);
        proof[0] = bytes32(uint256(paddle));            // low == paddle (membership)
        proof[1] = bytes32(uint256(paddle) + 1);        // high
        proof[2] = keccak256(abi.encode("sibling"));    // one sibling
    }

    function _nonMembershipProof(uint16 paddle) private pure returns (bytes32[] memory proof) {
        proof = new bytes32[](3);
        proof[0] = bytes32(uint256(paddle) - 1);        // low < paddle
        proof[1] = bytes32(uint256(paddle) + 1);        // high > paddle (brackets it)
        proof[2] = keccak256(abi.encode("sibling"));
    }

    // The canonical clean candidate. The first five distinct paddles land at slot indices 0..4 in
    // insertion order, so cleanBidder (the 4th ascending bid) sits at heapIndex 3 with the offender
    // the one strictly-higher slot at idx 4 (one preceding-flag-inclusion proof, for the offender).
    function _cleanCandidate(uint64 seq) private view returns (NextCleanCandidate memory c) {
        bytes32[][] memory preceding = new bytes32[][](1);
        preceding[0] = _flaggedProof(PADDLE_OFFENDER); // the one strictly-higher slot is flagged
        c = NextCleanCandidate({
            heapIndex: 3,
            bidder: cleanBidder,
            amount: AMT_CLEAN,
            paddleId: PADDLE_CLEAN,
            seq: uint40(seq),
            flagNonMembership: _nonMembershipProof(PADDLE_CLEAN),
            precedingFlagInclusion: preceding
        });
    }

    function _candidate(
        uint8 heapIndex,
        address bidder,
        uint128 amount,
        uint16 paddleId,
        uint64 seq
    ) private view returns (NextCleanCandidate memory c) {
        // Preceding-flag-inclusion proofs ordered by ASCENDING slot index (the order
        // _verifyAndPromote visits strictly-higher slots): idx 3 (PADDLE_CLEAN), then idx 4
        // (PADDLE_OFFENDER). Sized for the worst case (two strictly-higher slots).
        bytes32[][] memory preceding = new bytes32[][](2);
        preceding[0] = _flaggedProof(PADDLE_CLEAN);
        preceding[1] = _flaggedProof(PADDLE_OFFENDER);
        c = NextCleanCandidate({
            heapIndex: heapIndex,
            bidder: bidder,
            amount: amount,
            paddleId: paddleId,
            seq: uint40(seq),
            flagNonMembership: paddleId == 0 ? new bytes32[](0) : _nonMembershipProof(paddleId),
            precedingFlagInclusion: preceding
        });
    }

    // Deterministic forfeit-id used by these tests. The canonical derivation is a Treasury concern
    // and is not pinned by ITreasury, so this mirrors the Treasury's keccak(clone, offender, lotId).
    function _forfeitId(address offender_, uint256 lotId_) private view returns (bytes32) {
        return keccak256(abi.encode(address(auction), offender_, lotId_));
    }

    // Same placeholder for an ARBITRARY clone (parameterized rings build fresh clones).
    function _forfeitId2(address clone_, address offender_, uint256 lotId_) private pure returns (bytes32) {
        return keccak256(abi.encode(clone_, offender_, lotId_));
    }

    // Full ring builders.

    // Native rail: open the lot, fund 5 distinct paddles, place 5 ascending bids so the top-5 heap is
    // full (offender top + 4 clean below), then hammer. hammer moves the offender's committed into
    // escrowAmount.
    function _buildHammeredRingNative() private {
        _buildOpenRingNative();
        _hammerLot();
    }

    // The Open-phase ring (no hammer yet): five distinct paddles fill the heap, offender standing top.
    // Split out so a test that places a further bid while still Open (the full-heap re-bid) can inject
    // it before hammering.
    function _buildOpenRingNative() private {
        _initNative();
        _openLot();

        _depositNative(cleanBidder, BIG_DEPOSIT);
        _depositNative(offender, BIG_DEPOSIT);
        ringB3 = _mkBidder("ringB3", PADDLE_C3);
        ringB4 = _mkBidder("ringB4", PADDLE_C4);
        ringB5 = _mkBidder("ringB5", PADDLE_C5);

        // Ascending bids so each is a new strict top; final top is offender at AMT_OFFENDER. bidIndex
        // is the per-principal keyed nonce, so each bidder's only bid uses 0; the global bid sequence
        // (what candidate.seq mirrors) advances independently.
        _placeBidNative(ringB5, 0, AMT_C5, PADDLE_C5, 0);
        _placeBidNative(ringB4, 0, AMT_C4, PADDLE_C4, AMT_C5);
        _placeBidNative(ringB3, 0, AMT_C3, PADDLE_C3, AMT_C4);
        _placeBidNative(cleanBidder, 0, AMT_CLEAN, PADDLE_CLEAN, AMT_C3);
        _placeBidNative(offender, 0, AMT_OFFENDER, PADDLE_OFFENDER, AMT_CLEAN);
    }

    function _mkBidder(string memory label, uint16 paddleId) private returns (address a) {
        a = _bindSigner(label); // bound signing key so its ceiling sig recovers to it in placeBid
        fundEth(a, INITIAL_ETH);
        _mockPaddle(a, paddleId);
        _depositNative(a, BIG_DEPOSIT);
    }

    // Native 6-distinct-paddle ring on an arbitrary clone (heap min-replace tests). Six ascending
    // bids (each a new strict top): ringB5, ringB4, ringB3, cleanBidder, offender, then a 6th paddle
    // (PADDLE_C6) at `topAmt`. The first five fill slots 0..4 (slot 0 == the min, ringB5 @ AMT_C5),
    // then the 6th min-replaces slot 0, evicting ringB5, and becomes the top. Sets
    // ringB3/ringB4/ringB5/ringB6 and returns the 6th. Requires AMT_OFFENDER < topAmt <= BIG_DEPOSIT.
    function _buildHammeredRing6On(SessionAuction a, uint128 topAmt) private returns (address sixth) {
        InitConfig memory cfg = _defaultInitConfig(address(0));
        vm.prank(address(hammer));
        a.initialize(cfg);
        treasury.registerClone(address(a)); // register the ring clone as a forfeit depositor (idempotent)

        vm.prank(address(hammer));
        a.openLot(LOT, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));

        _depositNative2(a, cleanBidder, BIG_DEPOSIT);
        _depositNative2(a, offender, BIG_DEPOSIT);
        ringB3 = _mkBidderOn(a, "ringB3_6", PADDLE_C3, BIG_DEPOSIT);
        ringB4 = _mkBidderOn(a, "ringB4_6", PADDLE_C4, BIG_DEPOSIT);
        ringB5 = _mkBidderOn(a, "ringB5_6", PADDLE_C5, BIG_DEPOSIT);
        ringB6 = _mkBidderOn(a, "ringB6_6", PADDLE_C6, BIG_DEPOSIT);

        sixth = ringB6;

        // Ascending tops: slots fill 0..4 (slot 0 == ringB5 @ AMT_C5, the min), then the 6th
        // (topAmt > AMT_OFFENDER) min-replaces slot 0, evicting ringB5.
        _placeBidNativeOn(a, ringB5, 0, AMT_C5, PADDLE_C5, 0);
        _placeBidNativeOn(a, ringB4, 0, AMT_C4, PADDLE_C4, AMT_C5);
        _placeBidNativeOn(a, ringB3, 0, AMT_C3, PADDLE_C3, AMT_C4);
        _placeBidNativeOn(a, cleanBidder, 0, AMT_CLEAN, PADDLE_CLEAN, AMT_C3);
        _placeBidNativeOn(a, offender, 0, AMT_OFFENDER, PADDLE_OFFENDER, AMT_CLEAN);
        _placeBidNativeOn(a, ringB6, 0, topAmt, PADDLE_C6, AMT_OFFENDER);

        vm.warp(block.timestamp + 2 days);
        a.hammer(LOT);
    }

    // ERC-20 rail: a fresh clone initialized on the token rail, same ring, same hammer. Returns
    // the clone so the caller can drive voidAndAward on it.
    function _erc20HammeredRing() private returns (SessionAuction a) {
        a = SessionAuction(Clones.clone(address(impl)));
        vm.prank(address(hammer));
        a.initialize(_defaultInitConfig(address(token)));
        treasury.registerClone(address(a)); // register the erc20 ring clone as a forfeit depositor

        vm.prank(address(hammer));
        // Token-scaled reserve (6 decimals): a native-scale RESERVE_PRICE would reject every
        // token-scale bid (AMT_C5_T = 20e6) with BidTooLow.
        a.openLot(LOT, seller, uint96(1e6), uint64(block.timestamp + 1 days));

        _depositToken(a, cleanBidder, BIG_DEPOSIT_T);
        _depositToken(a, offender, BIG_DEPOSIT_T);

        address b3 = _bindSigner("erc20B3"); // bound signing keys so each ceiling sig recovers in placeBid
        address b4 = _bindSigner("erc20B4");
        address b5 = _bindSigner("erc20B5");
        fundToken(b3, INITIAL_TOKEN);
        fundToken(b4, INITIAL_TOKEN);
        fundToken(b5, INITIAL_TOKEN);
        _mockPaddle(b3, PADDLE_C3);
        _mockPaddle(b4, PADDLE_C4);
        _mockPaddle(b5, PADDLE_C5);
        _depositToken(a, b3, BIG_DEPOSIT_T);
        _depositToken(a, b4, BIG_DEPOSIT_T);
        _depositToken(a, b5, BIG_DEPOSIT_T);

        // Token-scaled bid amounts (6 decimals), same ascending shape as the native rail.
        _placeBidTokenOn(a, b5, 0, AMT_C5_T, PADDLE_C5, 0);
        _placeBidTokenOn(a, b4, 0, AMT_C4_T, PADDLE_C4, AMT_C5_T);
        _placeBidTokenOn(a, b3, 0, AMT_C3_T, PADDLE_C3, AMT_C4_T);
        _placeBidTokenOn(a, cleanBidder, 0, AMT_CLEAN_T, PADDLE_CLEAN, AMT_C3_T);
        _placeBidTokenOn(a, offender, 0, AMT_OFFENDER_T, PADDLE_OFFENDER, AMT_CLEAN_T);

        vm.warp(block.timestamp + 2 days);
        a.hammer(LOT);
    }

    // Token-scaled clean candidate (heapIndex 3, PADDLE_CLEAN, AMT_CLEAN_T) mirroring _cleanCandidate.
    function _cleanCandidateToken(uint64 seq) private view returns (NextCleanCandidate memory c) {
        bytes32[][] memory preceding = new bytes32[][](1);
        preceding[0] = _flaggedProof(PADDLE_OFFENDER);
        c = NextCleanCandidate({
            heapIndex: 3,
            bidder: cleanBidder,
            amount: AMT_CLEAN_T,
            paddleId: PADDLE_CLEAN,
            seq: uint40(seq),
            flagNonMembership: _nonMembershipProof(PADDLE_CLEAN),
            precedingFlagInclusion: preceding
        });
    }

    function _placeBidTokenOn(
        SessionAuction a,
        address principal,
        uint64 bidIndex,
        uint128 amount,
        uint16 paddleId,
        uint128 prevTop
    ) private {
        _mockPaddle(principal, paddleId);
        Ceiling memory c = _ceiling(principal, 16);
        AttestationQuote memory q = _quote(c, amount, bidIndex, prevTop, keccak256(abi.encode(principal, bidIndex)));
        bytes memory sig = _signCeiling(address(a), c, _signerKeyFor(principal));
        vm.prank(principal);
        a.placeBid(c, LOT, principal, bidIndex, amount, sig, _operatorKeyId(), q);
    }

    // Native placeBid on an ARBITRARY clone (parameterized rings build fresh clones).
    function _placeBidNativeOn(
        SessionAuction a,
        address principal,
        uint64 bidIndex,
        uint128 amount,
        uint16 paddleId,
        uint128 prevTop
    ) private {
        _mockPaddle(principal, paddleId);
        Ceiling memory c = _ceiling(principal, 16);
        AttestationQuote memory q = _quote(c, amount, bidIndex, prevTop, keccak256(abi.encode(principal, bidIndex)));
        bytes memory sig = _signCeiling(address(a), c, _signerKeyFor(principal));
        vm.prank(principal);
        a.placeBid(c, LOT, principal, bidIndex, amount, sig, _operatorKeyId(), q);
    }

    // Parameterized native ring (variable top-two amounts; for cap + fuzz tiers).
    // A fresh clone wired to `treasuryAddr`, same 5-distinct-paddle topology as
    // _buildHammeredRingNative: cleanBidder at heapIndex 3 (cleanAmt), offender the one strictly-higher
    // slot (offenderAmt), and an ascending ladder below cleanAmt. Requires offenderAmt > cleanAmt and
    // cleanAmt >= 5 ether (so the /5 floor stays >= RESERVE_PRICE).
    function _ringNativeOn(SessionAuction a, address treasuryAddr, uint128 offenderAmt, uint128 cleanAmt) private {
        InitConfig memory cfg = _defaultInitConfig(address(0));
        cfg.treasury = treasuryAddr;
        vm.prank(address(hammer));
        a.initialize(cfg);

        // A fresh ring clone must be a registered forfeit depositor or routeForfeit -> depositForfeit
        // reverts Unauthorized. Only register with the real treasury; the hostile reentrancy-treasury
        // path uses an inert mock that does not gate.
        if (treasuryAddr == address(treasury)) treasury.registerClone(address(a));

        vm.prank(address(hammer));
        a.openLot(LOT, seller, RESERVE_PRICE, uint64(block.timestamp + 1 days));

        uint256 big = 200_000 ether; // covers the largest fuzzed/cap clearing price
        fundEth(offender, big);
        fundEth(cleanBidder, big);
        _depositNative2(a, cleanBidder, big);
        _depositNative2(a, offender, big);

        address b3 = _mkBidderOn(a, "pB3", PADDLE_C3, big);
        address b4 = _mkBidderOn(a, "pB4", PADDLE_C4, big);
        address b5 = _mkBidderOn(a, "pB5", PADDLE_C5, big);

        // ascending ladder strictly below cleanAmt (each step >= 25%, well above min increment).
        uint128 c5 = cleanAmt / 5;
        uint128 c4 = cleanAmt / 4;
        uint128 c3 = cleanAmt / 3;
        _placeBidNativeOn(a, b5, 0, c5, PADDLE_C5, 0);
        _placeBidNativeOn(a, b4, 0, c4, PADDLE_C4, c5);
        _placeBidNativeOn(a, b3, 0, c3, PADDLE_C3, c4);
        _placeBidNativeOn(a, cleanBidder, 0, cleanAmt, PADDLE_CLEAN, c3);
        _placeBidNativeOn(a, offender, 0, offenderAmt, PADDLE_OFFENDER, cleanAmt);

        vm.warp(block.timestamp + 2 days);
        a.hammer(LOT);
    }

    function _hammeredRingNativeAt(uint128 offenderAmt, uint128 cleanAmt) private returns (SessionAuction a) {
        a = SessionAuction(Clones.clone(address(impl)));
        _ringNativeOn(a, address(treasury), offenderAmt, cleanAmt);
    }

    // A fresh clone wired to a CUSTOM (hostile) treasury, default amounts (for the reentrancy test).
    function _hammeredRingWithTreasury(address treasuryAddr) private returns (SessionAuction a) {
        a = SessionAuction(Clones.clone(address(impl)));
        _ringNativeOn(a, treasuryAddr, AMT_OFFENDER, AMT_CLEAN);
    }

    function _depositNative2(SessionAuction a, address principal, uint256 amount) private {
        vm.prank(principal);
        a.depositCeiling{value: amount}(LOT, amount);
    }

    function _mkBidderOn(SessionAuction a, string memory label, uint16 paddleId, uint256 amount)
        private
        returns (address acct)
    {
        acct = _bindSigner(label); // bound signing key so its ceiling sig recovers to it in placeBid
        fundEth(acct, amount + 1 ether);
        _mockPaddle(acct, paddleId);
        _depositNative2(a, acct, amount);
    }

    // Clean candidate with a parameterized promoted amount (mirrors _cleanCandidate's topology:
    // heapIndex 3, PADDLE_CLEAN, offender the one strictly-higher slot).
    function _cleanCandidateAt(uint64 seq, uint128 amount) private view returns (NextCleanCandidate memory c) {
        bytes32[][] memory preceding = new bytes32[][](1);
        preceding[0] = _flaggedProof(PADDLE_OFFENDER);
        c = NextCleanCandidate({
            heapIndex: 3,
            bidder: cleanBidder,
            amount: amount,
            paddleId: PADDLE_CLEAN,
            seq: uint40(seq),
            flagNonMembership: _nonMembershipProof(PADDLE_CLEAN),
            precedingFlagInclusion: preceding
        });
    }
}

// Hostile Treasury used only by test_RevertWhen_VoidReentered. On depositForfeit it re-enters the
// calling clone's voidAndAward to attack the nonReentrant guard. All other ITreasury methods are inert.
contract D_ReentrantTreasury is ITreasury {
    SessionAuction private _target;
    uint256 private _lotId;
    bytes32[] private _proof;
    NextCleanCandidate private _cand;
    bool private _armed;

    function arm(SessionAuction target, uint256 lotId, bytes32[] memory proof, NextCleanCandidate memory cand)
        external
    {
        _target = target;
        _lotId = lotId;
        _proof = proof;
        _cand = cand;
        _armed = true;
    }

    function depositForfeit(address, address, uint256, uint256, uint256, uint256, address)
        external
        payable
        returns (bytes32)
    {
        if (_armed) {
            // Re-enter the void on the same clone: the nonReentrant guard MUST reject this.
            _target.voidAndAward(_lotId, _proof, _cand);
        }

        return bytes32(0);
    }

    function challenge(bytes32) external payable {}
    function resolveChallenge(bytes32, bool) external {}
    function disburse(bytes32) external {}
    function registerClone(address) external {}
}
