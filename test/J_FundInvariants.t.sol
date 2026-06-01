// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Fund-safety invariants: stateful Foundry invariant_* tests plus a handler, run on BOTH rails
// (native and ERC-20 concretes inherit one handler-driven base):
//   invariant_FundConservation         -> per-token conservation from the handler's own cumulative
//                                          accounting: cloneBalance + paidOut == fundedIn
//                                          (rail-agnostic), plus a getter-based cross-check and
//                                          three-pool separation.
//   invariant_EscrowSingleExit         -> lot.escrowAmount is set once, zeroed by exactly one exit,
//                                          never resurrected; companion tests assert every
//                                          escrow-paying call fails closed with its exact selector.
//   invariant_DisputeBondPoolIsolation -> the dispute-bond pool (lot.disputeBond) is a closed,
//                                          conserved pool disjoint from bid escrow; inflow tracked
//                                          from the openDispute pull, bond out == bond in, pool never
//                                          exceeds funded-in.
//   test_StorageLayoutBaseline + split -> structural pin on the packed Lot layout, plus per-region
//                                          selector exercises split into independent tests.
//   invariant_ClassBGateMonotonicity   -> lot.bidIntegrityOpen moves +1 only on challengeAttestation,
//                                          -1 only on resolve/timeout, never negative, gate open iff
//                                          net>0; challengeOverCeiling never flips it.
//   invariant_NoStrandReachability     -> the terminals have no outward escrow edge (escrowAmount
//                                          stays 0 once terminal); every non-terminal lot retains a
//                                          counterparty-independent exit (reclaim/releaseAfterWindow/
//                                          timeout).
//   invariant_NonceReplayMonotonicity  -> a consumed bidIndex per (principal, nonceKey) can never be
//                                          replayed and a used quote nonce per (operatorKeyId, nonce)
//                                          can never be reused.
//
// fail_on_revert is false: handler actions swallow reverts, so a reverted call leaves state unchanged
// and the conservation predicate still holds. afterInvariant() is a liveness gate asserting the key
// fund-moving action succeeded at least once, so the invariants can never pass vacuously. The negative
// selector exercises (fail-closed escrow paths, the split region drivers, the nonce/quote replay
// re-drives) assert the exact canonical errors.

import {HammerBase} from "./HammerBase.t.sol";
import {Vm} from "forge-std/Vm.sol";
import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";

import {SessionAuction} from "../src/SessionAuction.sol";
import {ISessionAuction} from "../src/interfaces/ISessionAuction.sol";
import {MockERC20} from "./mocks/MockERC20.sol";

import {
    Ceiling,
    AttestationQuote,
    NextCleanCandidate,
    InitConfig,
    Lot,
    Deposit,
    IntegrityDispute,
    Resolution,
    LotPhase,
    DeliveryState,
    CEILING_TYPEHASH
} from "../src/types/HammerTypes.sol";

// Handler: drives randomized sequences of the real SessionAuction entrypoints across multiple lots,
// principals, and a configurable rail, and ghost-tracks every fund bucket the invariants assert on.
// Every action wraps the call in a try/catch: a fail-closed guard may revert, the run must continue,
// and a reverted call leaves state unchanged.
//
// Fund accounting model. The ISessionAuction surface exposes no getter for a deposit's locked
// committed term (only withdrawableFree, the free term) and none for the integrity-dispute bond, so a
// balance sum read from chain is structurally incomplete. Conservation is asserted instead from the
// handler's own cumulative accounting, which needs neither missing getter:
//   - totalFundedIn: incremented by the exact amount pulled in on every successful pull-side action
//     (depositCeiling, openDispute bond, challengeAttestation integrity bond). A mint/skim on a pull
//     would break cloneBalance == fundedIn - paidOut.
//   - totalPaidOut: incremented by the observed outflow (pre-call minus post-call cloneBalance, when
//     funds left) on every successful push-side action (withdraw / claim / release / refund /
//     reclaim / resolve / withdrawRefund). A failed push credits the caller's pending withdrawal and
//     leaves the funds in the clone, so no outflow is observed.
// The identity cloneBalance == totalFundedIn - totalPaidOut then holds after every call on both
// rails. The getter-based bucket sum is retained only as a <= cross-check for the buckets that do
// have getters (escrowAmount, disputeBond, free, pending).
contract FundInvariantsHandler {
    // Canonical cheatcode address so the handler can prank as the picked principal, keeping
    // deposits / bids / withdrawals / bonds keyed to the same identity the invariant sweep sums over.
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    SessionAuction internal immutable auction;
    MockERC20 internal immutable token; // ERC-20 rail; ignored on the native rail
    bool internal immutable nativeRail;

    // The reentrant adversary (a registered principal). Held so rearmAttacker can rotate which exit it
    // re-enters during the run (releaseAfterWindow / claimPending / reclaimUndelivered / withdrawRefund,
    // not only withdrawDeposit). Set via setAttacker. A double-fire from any rotated exit breaks
    // conservation and single-exit.
    FundReentrantRecipient internal reentrantAttacker;

    // Lot id space and seq space, small and fixed so the fuzzer densely explores collisions (same lot,
    // different principal; same (lot, seq) for challenge/resolve/timeout so the Class B gate opens and
    // closes).
    uint256 internal constant LOT_COUNT = 3;
    uint64 internal constant SEQ_COUNT = 3;

    // Bond sizes mirrored from HammerBase (the handler is a plain contract, not a subclass). The
    // entrypoints require msg.value (or the pulled token amount) to equal these exactly.
    uint256 internal constant DISPUTE_BOND = 0.1 ether;
    uint256 internal constant INTEGRITY_BOND = 0.1 ether;

    // Reserve floor (HammerBase RESERVE_PRICE) so a deposit clears DepositBelowReserve.
    uint256 internal constant RESERVE = 1 ether;

    // Settlement fee in bps (HammerBase FEE_BPS). resolve() uses it to compute the exact escrow leg paid
    // to the winner under ReleaseToSeller (escrow - mulDiv(escrow, FEE_BPS, 1e4)), so the recipient
    // check can pin the winner's gain to escrow-leg + bond exactly, not merely the >= bond lower bound.
    uint256 internal constant FEE_BPS = 250; // 2.5%

    // Frozen delivery-phase exit windows (HammerBase). The no-strand liveness ghost arms only when the
    // matching exit's exact precondition holds (state + frozen window).
    uint256 internal constant SELLER_DELIVER_SEC = 7 days; // == HammerBase.SELLER_DELIVER_SEC
    uint256 internal constant DISPUTE_WINDOW_SEC = 3 days;  // == HammerBase.DISPUTE_WINDOW_SEC

    // Set once the session is voided (voidWholeSession). Under a void the delivery-phase exits become
    // withdrawRefund, not reclaim/release, so the unconditional-exit liveness ghost must not arm.
    bool internal sessionWasVoided;

    address[] internal principals;

    // Ghost: lot ids the handler has ever touched, for the invariant sweep.
    uint256[] internal touchedLots;
    mapping(uint256 => bool) internal lotKnown;

    // Conservation ghosts (rail-agnostic; never read address(this).balance as truth).
    uint256 public totalFundedIn; // exact pull-in intent (deposits + dispute bonds + integrity bonds)
    uint256 public totalPaidOut; // observed clone outflow on push-side actions
    uint256 internal preCloneBal; // pre-call clone balance snapshot, set at the top of each action

    // Cumulative intent pulled into the two buckets with no getter (a deposit's locked committed term,
    // the integrity-dispute bond). Used in a lower-bound cross-check (getterSum + theseIntents >=
    // cloneBal): catches held funds that escaped both the readable getters and these intents. Both are
    // monotonic over-estimates of the currently-held unreadable balance (committed migrates to readable
    // escrow at hammer or to readable free on outbid; the integrity bond leaves on resolve/timeout),
    // which is safe for a >= bound and is exactly 0 when no bid lands. Full equality would need the
    // missing getters.
    uint256 public committedByIntent; // free->committed locked by a successful placeBid (no-getter bucket)
    uint256 public integrityBondByIntent; // integrity bond pulled by challengeAttestation (no-getter bucket)

    // Escrow single-exit ghosts. Per lot: count of escrowAmount nonzero -> zero transitions (must stay
    // <= 1), the last observed escrowAmount, a "zeroed after being set" flag, and a "resurrected" flag
    // (escrow nonzero again after a zeroing).
    mapping(uint256 => uint256) public escrowZeroings;
    mapping(uint256 => uint128) internal lastEscrow;
    mapping(uint256 => bool) internal escrowZeroed;
    mapping(uint256 => bool) public escrowResurrected;

    // Set-once detector: escrowAmount observed going from one nonzero value to a different nonzero value
    // with no intervening zeroing. escrowAmount is written exactly once, so this must never trip, except
    // for the one legal promote re-snapshot tracked below.
    mapping(uint256 => bool) public escrowMutatedWhileNonzero;

    // Legal-promote re-snapshot accounting. At voidAndAward escrowAmount is re-snapshotted for the
    // promoted winner inside one external call: the offender's escrow E1 is zeroed (E1 -> 0), then the
    // promoted escrow E2 is set (0 -> E2). _sync sees only the call endpoints (E1 then E2), never the
    // intervening zero, so a compliant promote looks like a nonzero -> different-nonzero step that would
    // false-trip escrowMutatedWhileNonzero. The Hammered -> Voided phase transition identifies it: on it
    // _sync counts escrowResnapshots and does not flag set-once; escrowResnapshots <= 1 is asserted
    // instead (a second promote re-snapshot trips). escrowZeroings is not touched here, so the offender's
    // E1 leaving and the promoted E2 arriving collapse into one re-snapshot and escrowZeroings stays the
    // final terminal exit (E2 -> 0). Every other nonzero -> different-nonzero transition still trips
    // escrowMutatedWhileNonzero, notably a phase==Awaiting finalize-time re-snapshot (a forbidden second
    // escrow lock).
    mapping(uint256 => uint8) internal lastPhase; // last observed LotPhase per lot (promote-transition detector)
    mapping(uint256 => uint256) public escrowResnapshots; // count of legal promote-time escrow re-snapshots (<= 1)

    // Dispute-bond pool ghosts (the lot.disputeBond pool only; the integrity bond is separate).
    // bondPulledIn comes from the openDispute pull, not inferred from disputeBond deltas (which can both
    // miss and double-count). bondPaidOut is the observed disputeBond zero-transition (a payout to the
    // winning party, or to the opener when a void returns the bond).
    uint256 public bondPulledIn;
    uint256 public bondPaidOut;
    mapping(uint256 => uint96) internal lastBond;

    // Class B gate monotonicity ghosts (per lot).
    mapping(uint256 => uint256) public classBOpens; // successful challengeAttestation count
    mapping(uint256 => uint256) public classBCloses; // successful resolveBidIntegrityDispute + timeout count
    mapping(uint256 => uint256) public classAActions; // successful challengeOverCeiling count (must never open the gate)

    // Gate-blocks-release, phase coupling: _release is reachable only when bidIntegrityOpen == 0, so a lot
    // must not advance to Settled while its gate is open. Set by _flagReleaseThroughGate, which snapshots
    // the gate and phase before a release-driving call (confirm / releaseWindow / resolve / finalize) and
    // flags a real advance to Settled while the gate was open at the attempt. Reading the gate at the
    // attempt keeps the coupling sound even if that same action (or a prior resolve/timeout) clears the
    // gate before _sync, which a post-call read would miss.
    mapping(uint256 => bool) public releasedWhileGateOpen;

    // Gate-blocks-release, fund coupling. The gate exists to keep escrow funds from leaving while a Class
    // B dispute is open. A buggy _release that pays the seller through an open gate but skips the terminal
    // Settled write slips the phase coupling above yet leaks escrow. Set when, across a release-driving
    // call whose gate was open at the attempt, lot.escrowAmount went nonzero -> zero. Conservation stays
    // neutral on such a release (escrow out == paidOut), so this is not redundant with it. Stays unset
    // until a Class-B-disputed lot reaches a release attempt.
    mapping(uint256 => bool) public escrowPaidWhileGateOpen;

    // Terminal no-strand ghosts (per lot).
    mapping(uint256 => bool) public sawTerminal; // a terminal phase (Settled/Refunded/NoSale) was observed
    mapping(uint256 => bool) public escrowAfterTerminal; // nonzero escrow observed after a terminal phase (illegal)

    // Liveness half: from every non-terminal delivery state a counterparty-independent exit must exist.
    // Per lot, ghost whether it ever rested non-terminal while holding escrow in a state with an
    // unconditional independent exit (AwaitingDelivery -> reclaimUndelivered, Delivered ->
    // releaseAfterWindow), whether the clock was warped past its frozen-anchor window, whether that exit
    // was driven post-warp, and whether the lot then reached a terminal phase. A lot armed and warped
    // whose exit leaves it still non-terminal is a strand.
    mapping(uint256 => bool) public sawNonTerminalWithEscrow; // observed in a non-terminal delivery state holding escrow
    mapping(uint256 => bool) public warpedPastWindow; // block.timestamp advanced past this lot's frozen exit window
    mapping(uint256 => bool) public independentExitAttempted; // a counterparty-independent exit was driven post-warp
    mapping(uint256 => bool) public reachedTerminalAfterExit; // the lot reached a terminal phase after that exit

    // Nonce / quote replay ghosts: how many times placeBid succeeded with that exact (principal, nonceKey,
    // bidIndex) / (operatorKeyId, quote.nonce). A strictly-sequential nonce ladder and a one-shot quote
    // nonce mean each must be <= 1.
    mapping(bytes32 => uint256) public bidIndexSuccessCount; // key: hash(principal, nonceKey, bidIndex)
    mapping(bytes32 => uint256) public quoteNonceSuccessCount; // key: hash(operatorKeyId, quote.nonce)

    // Dispute-bond recipient ghost. Conservation is blind to a bond paid to the wrong party; the bond must
    // reach exactly the winning party (seller under ReleaseToSeller, buyer/highBidder under RefundToBuyer).
    // bondToWrongParty trips if, across a resolveDispute that paid the bond out (disputeBond nonzero -> 0),
    // the credited party (pendingWithdrawal/balance delta) was not the rule-correct recipient.
    mapping(uint256 => bool) public bondToWrongParty;

    // Exact-recipient ghost. bondToWrongParty's "winner gained >= bond" / "loser unchanged" checks are
    // lower bounds the winner's own escrow leg already satisfies, so a bond misrouted to a third party
    // (feeRecipient/arbiter/attacker) slips both. This trips if, across a resolveDispute that paid the
    // bond out, the winner's claimable did not rise by exactly (escrow leg + bond) or the feeRecipient's
    // did not rise by exactly the fee (ReleaseToSeller) / moved at all (RefundToBuyer, where _release
    // never runs). Either deviation means the bond was split, dropped, or redirected.
    mapping(uint256 => bool) public bondNotExactToWinner;

    // afterInvariant liveness counters (guard against a vacuous green run).
    uint256 public depositSuccesses;

    // Gates the strengthened per-subject liveness asserts in afterInvariant. Escrow, dispute bonds, and
    // the Class B gate are all downstream of an accepted bid, so they cannot advance until placeBid lands;
    // gating those asserts on bidSuccesses > 0 keeps them dormant until bids land and makes them bite the
    // moment they do. The unconditional depositSuccesses gate is the primary vacuity signal (depositCeiling
    // needs no bid).
    uint256 public bidSuccesses;

    // Attestation kit, threaded from the base so the handler (a non-HammerBase contract) can build a
    // passing placeBid: a real EIP-712 ceiling sig recovering to the principal plus a real low-S P-256
    // operator quote over the canonical action digest.
    uint256 internal constant P256_ORDER =
        0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551;
    uint256 internal constant P256_HALF =
        0x7fffffff800000007fffffffffffffffde737d56d38bcf4279dce5617e3192a8;
    bytes32 internal constant EIP712_TYPE_HASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 internal constant HASHED_NAME = keccak256(bytes("Hammer"));
    bytes32 internal constant HASHED_VERSION = keccak256(bytes("1"));

    uint256 internal immutable operatorPk;   // operator secp256r1 private key (signs quotes)
    bytes32 internal immutable operatorKeyId; // registered keyId; placeBid's operatorKeyId arg
    bytes32 internal immutable sessionId;     // == clone SESSION_ID (binds the ceiling + nonceKey + digest)
    bytes32 internal immutable mrEnclave;     // pinned measurement (must match the quote, else fail-closed)
    bytes32 internal immutable vendorRoot;
    mapping(address principal => uint256 ecdsaKey) internal keyOf; // 0 for the attacker contract (no key)
    uint256 internal quoteNonceCounter; // monotonic so every landed bid carries a fresh one-shot quote nonce

    // Per (lotId, seq) the (maxBid, salt) the handler committed, so the reveal action can re-open it
    // (reveal checks keccak256(abi.encode(maxBid, salt)) == ceilingCommit).
    struct RevealData { uint128 maxBid; bytes32 salt; bool set; }
    mapping(uint256 lotId => mapping(uint64 seq => RevealData)) internal revealOf;

    constructor(
        SessionAuction _auction,
        MockERC20 _token,
        bool _nativeRail,
        address[] memory _principals,
        uint256[] memory _principalKeys,
        uint256 _operatorPk,
        bytes32 _operatorKeyId,
        bytes32 _sessionId,
        bytes32 _mrEnclave,
        bytes32 _vendorRoot
    ) {
        auction = _auction;
        token = _token;
        nativeRail = _nativeRail;
        principals = _principals;
        operatorPk = _operatorPk;
        operatorKeyId = _operatorKeyId;
        sessionId = _sessionId;
        mrEnclave = _mrEnclave;
        vendorRoot = _vendorRoot;
        // Bind each principal's ECDSA signing key (0 == cannot sign a ceiling, e.g. the attacker).
        for (uint256 i = 0; i < _principals.length; i++) {
            keyOf[_principals[i]] = _principalKeys[i];
        }
    }

    /// @notice Wire the reentrant adversary so rearmAttacker can rotate its re-entry target during the run.
    ///         Called once from setUp after the attacker is constructed.
    function setAttacker(FundReentrantRecipient _attacker) external {
        reentrantAttacker = _attacker;
    }

    // Attestation kit (handler-local). Lets the handler build a passing bid. Reads only immutables +
    // constants + pure cheatcodes (vm.sign / vm.signP256 are declared pure in Vm.sol), so the view/pure
    // markers are valid here.

    /// @dev The keyed-nonce key the ceiling binds for `principal` on `lotId`:
    ///      uint192(uint256(keccak256(abi.encode(sessionId, lotId, principal)))).
    function _nonceKeyOf(uint256 lotId, address principal) internal view returns (uint192) {
        return uint192(uint256(keccak256(abi.encode(sessionId, lotId, principal))));
    }

    function _domainSeparator() internal view returns (bytes32) {
        return keccak256(abi.encode(EIP712_TYPE_HASH, HASHED_NAME, HASHED_VERSION, block.chainid, address(auction)));
    }

    /// @dev Real EIP-712 ceiling signature over the clone domain (ECDSA, recovers to c.principal).
    function _signCeiling(Ceiling memory c, uint256 key) internal view returns (bytes memory) {
        bytes32 structHash = keccak256(
            abi.encode(
                CEILING_TYPEHASH, c.principal, c.sessionId, c.lotId,
                c.ceilingCommit, c.strategy, c.deadline, c.maxBids, c.nonceKey
            )
        );
        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", _domainSeparator(), structHash));
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(key, digest);
        return abi.encodePacked(r, s, v);
    }

    /// @dev P-256 sign `digest` with `pk`, low-S normalized (P256.verify rejects high-S).
    function _signP256LowS(uint256 pk, bytes32 digest) internal pure returns (bytes32 r, bytes32 s) {
        (r, s) = vm.signP256(pk, digest);
        if (uint256(s) > P256_HALF) s = bytes32(P256_ORDER - uint256(s));
    }

    /// @dev The canonical 10-field action digest placeBid reconstructs and P256.verify checks.
    function _actionDigest(Ceiling memory c, uint256 lotId, uint128 amount, uint64 bidIndex, AttestationQuote memory q)
        internal
        view
        returns (bytes32)
    {
        return keccak256(
            abi.encode(
                sessionId, lotId, amount, c.nonceKey, bidIndex,
                c.ceilingCommit, q.nonce, q.mrEnclave, q.vendorRoot, q.observedPrevTop
            )
        );
    }

    /// @dev A measurement-correct quote carrying a REAL P-256 attestation by the seeded operator key over
    ///      the canonical digest of (c, lotId, amount, bidIndex, thisQuote). observedPrevTop MUST equal the
    ///      on-chain lot.highBid or placeBid reverts StalePrevTop.
    function _realQuote(
        Ceiling memory c,
        uint256 lotId,
        uint128 amount,
        uint64 bidIndex,
        uint128 observedPrevTop,
        bytes32 nonce
    ) internal view returns (AttestationQuote memory q) {
        q = AttestationQuote({
            mrEnclave: mrEnclave,
            vendorRoot: vendorRoot,
            observedPrevTop: bytes32(uint256(observedPrevTop)),
            nonce: nonce,
            r: bytes32(0),
            s: bytes32(0)
        });
        (q.r, q.s) = _signP256LowS(operatorPk, _actionDigest(c, lotId, amount, bidIndex, q));
    }

    // Internal book-keeping.

    function _noteLot(uint256 lotId) internal {
        if (!lotKnown[lotId]) {
            lotKnown[lotId] = true;
            touchedLots.push(lotId);
        }
    }

    /// @dev Rail-aware clone balance. Folded into the outflow ghost, never used as the conservation
    ///      source of truth.
    function _cloneBalance() internal view returns (uint256) {
        return nativeRail ? address(auction).balance : token.balanceOf(address(auction));
    }

    /// @dev Snapshot the clone balance at the start of an action so _sync can fold the post-call outflow
    ///      into totalPaidOut. Pull-side intent is added separately in each action's success branch.
    function _before() internal {
        preCloneBal = _cloneBalance();
    }

    /// @dev Re-read the lot after any call and fold escrow / bond transitions + clone outflow into the
    ///      ghosts. Reads only on-chain truth, so a reverted call (state unchanged) is a no-op.
    function _sync(uint256 lotId) internal {
        Lot memory lot = auction.getLot(lotId);

        // OUTFLOW: any net decrease in the clone balance over this call is a payout that left the clone (a
        // failed push credits the caller's pending withdrawal and leaves funds in, so causes no decrease).
        // preCloneBal is advanced to post so a second _sync in the same action (voidWholeSession loops over
        // every lot) does not double-count the same outflow.
        uint256 post = _cloneBalance();
        if (post < preCloneBal) {
            totalPaidOut += (preCloneBal - post);
        }
        preCloneBal = post;

        // Escrow single-exit accounting + resurrection / set-once / terminal-strand detection.
        uint128 esc = lot.escrowAmount;

        if (lastEscrow[lotId] != 0 && esc == 0) {
            escrowZeroings[lotId] += 1; // a nonzero -> zero transition: at most one is ever allowed
            escrowZeroed[lotId] = true;
        }

        // escrow nonzero again after a zeroing: a re-snapshot bug.
        if (escrowZeroed[lotId] && esc != 0) {
            escrowResurrected[lotId] = true;
        }

        uint8 ph = lot.phase;

        // Set-once: escrow overwritten from one nonzero value to a different nonzero value with no
        // intervening zeroing. escrowAmount is written exactly once, so this must never happen except for
        // the legal promote re-snapshot at voidAndAward (E1 -> 0 -> E2 within one call, seen as the
        // endpoints E1 -> E2), recognized by the Hammered -> Voided transition and counted in
        // escrowResnapshots (asserted <= 1) instead of flagged. Every other nonzero -> different-nonzero
        // transition trips escrowMutatedWhileNonzero (e.g. a phase==Awaiting finalize-time second lock).
        if (lastEscrow[lotId] != 0 && esc != 0 && esc != lastEscrow[lotId]) {
            bool legalPromote =
                ph == uint8(LotPhase.Voided) && lastPhase[lotId] == uint8(LotPhase.Hammered);

            if (legalPromote) {
                escrowResnapshots[lotId] += 1; // the single allowed promote-time re-snapshot
            } else {
                escrowMutatedWhileNonzero[lotId] = true;
            }
        }

        lastEscrow[lotId] = esc;
        lastPhase[lotId] = ph;

        // No-strand absorbing half: once a lot reaches a terminal phase, escrow must stay 0.
        if (ph == uint8(LotPhase.Settled) || ph == uint8(LotPhase.Refunded) || ph == uint8(LotPhase.NoSale)) {
            sawTerminal[lotId] = true;
        }

        if (sawTerminal[lotId] && esc != 0) {
            escrowAfterTerminal[lotId] = true;
        }

        // No-strand liveness half: record a lot resting non-terminal with escrow held in a state with an
        // unconditional counterparty-independent exit: AwaitingDelivery (reclaimUndelivered after the
        // frozen awaitingAt + sellerDeliverSec) or Delivered (releaseAfterWindow after the frozen
        // deliveredAt + disputeWindowSec). Disputed is excluded: its only independent escape (withdrawRefund
        // returning the bond to the opener for a vanished arbiter) is conditional on a prior voidSession, a
        // two-call composition pinned by test_NoStrand_WithdrawRefundNotAnchoredOnEndsAt.
        uint8 ds = lot.deliveryState;
        bool nonTerminalUnconditionalExit =
            (ds == uint8(DeliveryState.AwaitingDelivery) || ds == uint8(DeliveryState.Delivered));

        if (nonTerminalUnconditionalExit && esc != 0) {
            sawNonTerminalWithEscrow[lotId] = true;
        }

        // independentExitAttempted is armed only when the matching exit's exact precondition held (state +
        // frozen window + gate/void scoping), so it implies the window passed; the terminal here is the
        // same-call settle the exit drove. Release maps to Settled, the reclaim/refund path to Refunded.
        if (independentExitAttempted[lotId] && (ph == uint8(LotPhase.Settled) || ph == uint8(LotPhase.Refunded))) {
            reachedTerminalAfterExit[lotId] = true;
        }

        // Gate-blocks-release is handled by _flagReleaseThroughGate, which snapshots the gate + phase +
        // escrow before each release-driving call. No detector here: once bids land, challengeAttestation
        // can open a Class B dispute on an already-settled lot (it gates on the integrity window + seq
        // existence, not the phase), and that benign post-settlement slash record is indistinguishable at
        // sync time from a release through an open gate. See test_ClassBGateBlocksRelease and
        // test_PostSettleClassBDoesNotFalseTripGateDetector.

        // Dispute-bond accounting: detect the bond moving from held to zero (a payout). Inflow is added
        // from the openDispute pull, not inferred here; only the payout side is read.
        uint96 bond = lot.disputeBond;

        if (lastBond[lotId] != 0 && bond == 0) {
            bondPaidOut += lastBond[lotId];
        }

        lastBond[lotId] = bond;
    }

    /// @dev Gate-blocks-release: snapshot the Class B gate, lot phase, and held escrow before a
    ///      release-driving call, for _flagReleaseThroughGate to consume after. Reading the gate at the
    ///      release attempt means the coupling does not rest on the post-call gate read, which a
    ///      same-action or prior resolve/timeout can clear.
    function _snapGate(uint256 lotId) internal view returns (bool gateWasOpen, uint8 prePhase, uint128 preEscrow) {
        Lot memory lot = auction.getLot(lotId);
        gateWasOpen = auction.bidIntegrityDisputeOpen(lotId);
        prePhase = lot.phase;
        preEscrow = lot.escrowAmount;
    }

    /// @dev Gate-blocks-release post-call leg, two couplings.
    ///      Phase (releasedWhileGateOpen): flag iff the lot advanced to Settled (prePhase != Settled,
    ///      postPhase == Settled) while the gate was open at the attempt.
    ///      Fund (escrowPaidWhileGateOpen): flag iff escrow went nonzero -> zero across the call while the
    ///      gate was open at the attempt, regardless of phase. Catches a release that pays the seller
    ///      through an open gate but skips the terminal phase write (which the phase coupling misses).
    ///      Both scoped to a real advance / escrow exit so a no-op on an already-Settled / already-empty lot
    ///      never false-trips.
    function _flagReleaseThroughGate(uint256 lotId, bool gateWasOpen, uint8 prePhase, uint128 preEscrow) internal {
        if (!gateWasOpen) return;

        Lot memory lot = auction.getLot(lotId);

        if (prePhase != uint8(LotPhase.Settled) && lot.phase == uint8(LotPhase.Settled)) {
            releasedWhileGateOpen[lotId] = true;
        }

        if (preEscrow != 0 && lot.escrowAmount == 0) {
            escrowPaidWhileGateOpen[lotId] = true;
        }
    }

    function _pick(uint256 seed) internal view returns (address) {
        return principals[seed % principals.length];
    }

    function _lot(uint256 seed) internal pure returns (uint256) {
        return seed % LOT_COUNT;
    }

    function _seq(uint64 seed) internal pure returns (uint64) {
        return seed % SEQ_COUNT;
    }

    // Driven actions. Each is a thin wrapper that builds plausible calldata and swallows reverts. The
    // targeted selectors cover the whole money path (deposit, bid, hammer, finalize, deliver, dispute,
    // resolve, exit).

    function deposit(uint256 lotSeed, uint256 whoSeed, uint128 amount) external {
        uint256 lotId = _lot(lotSeed);
        address who = _pick(whoSeed);

        // Bound to >= reserve so a green deposit clears DepositBelowReserve.
        amount = uint128(bound(amount, RESERVE, 100 ether));

        _noteLot(lotId);
        _before();

        if (nativeRail) {
            vm.deal(who, who.balance + amount); // ensure the principal can fund the value call
            vm.prank(who);
            try auction.depositCeiling{value: amount}(lotId, amount) {
                totalFundedIn += amount;
                depositSuccesses += 1;
            } catch {}
        } else {
            // ERC-20 rail: mint to + approve the clone from the principal, then deposit as them.
            token.mint(who, amount);
            vm.prank(who);
            token.approve(address(auction), amount);
            vm.prank(who);
            try auction.depositCeiling(lotId, amount) {
                totalFundedIn += amount;
                depositSuccesses += 1;
            } catch {}
        }

        _sync(lotId);
    }

    function withdraw(uint256 lotSeed, uint256 whoSeed, uint128 amount) external {
        uint256 lotId = _lot(lotSeed);
        address who = _pick(whoSeed);
        _noteLot(lotId);
        _before();

        amount = uint128(bound(amount, 0, 100 ether));

        vm.prank(who);
        try auction.withdrawDeposit(lotId, amount) {} catch {}

        _sync(lotId);
    }

    /// @notice Build and submit a real bid (passing ceiling sig + P-256 operator quote) so the fuzzer
    ///         lands bids. The seed steers the amount only; the bidIndex is the live keyed nonce so the
    ///         ordered-nonce gate passes. The attacker principal (no signing key) is skipped; it stays in
    ///         the set for the withdraw/reentry paths.
    function placeBid(uint256 lotSeed, uint256 whoSeed, uint128 amount, uint64 /*bidIndexSeed*/) external {
        uint256 lotId = _lot(lotSeed);
        address who = _pick(whoSeed);
        _noteLot(lotId);
        _before();

        uint256 key = keyOf[who];

        if (key != 0) {
            _attemptRealBid(lotId, who, key, amount);
        }

        _sync(lotId);
    }

    /// @dev The landing-bid builder (split out to keep placeBid's stack shallow). Bounds the amount into
    ///      the valid (highBid, free] window so the bid lands when there is funded headroom; the try/catch
    ///      tolerates the states where it cannot (lot closed / past endsAt / no free / gate open).
    function _attemptRealBid(uint256 lotId, address who, uint256 key, uint128 amountSeed) internal {
        Lot memory lot = auction.getLot(lotId);
        uint128 highBid = lot.highBid;

        // free term backing this bid: a non-top bidder's committed is 0, a self-outbid releases its own
        // committed first, so `free >= amount` is the funded condition placeBid enforces.
        uint128 free = uint128(auction.withdrawableFree(lotId, who));
        uint128 floor = lot.highBidder == address(0) ? uint128(RESERVE) : highBid + 1; // strictly over the top
        uint128 amount = free >= floor
            ? uint128(bound(amountSeed, floor, free)) // backable + top-beating -> lands
            : uint128(bound(amountSeed, floor, floor + 1 ether)); // no headroom -> exercises the revert path

        uint192 nonceKey = _nonceKeyOf(lotId, who);
        uint64 bidIndex = uint64(auction.nonces(who, nonceKey)); // the live keyed nonce: ordered, so it lands
        bytes32 salt = keccak256(abi.encode("J-ceiling-salt", lotId, who, bidIndex));
        Ceiling memory c = Ceiling({
            principal: who,
            sessionId: sessionId,
            lotId: lotId,
            ceilingCommit: keccak256(abi.encode(amount, salt)), // maxBid == amount, openable by `reveal`
            strategy: 0,
            deadline: uint64(block.timestamp + 1 days),
            maxBids: 64,
            nonceKey: nonceKey
        });
        bytes memory sig = _signCeiling(c, key);
        bytes32 qnonce = keccak256(abi.encode("J-quote-nonce", quoteNonceCounter));
        quoteNonceCounter += 1;
        AttestationQuote memory q = _realQuote(c, lotId, amount, bidIndex, highBid, qnonce); // observedPrevTop==highBid

        try auction.placeBid(c, lotId, who, bidIndex, amount, sig, operatorKeyId, q) {
            // This bid consumed exactly (principal, nonceKey, bidIndex) and (operatorKeyId, quote.nonce); a
            // sequential ladder + one-shot quote nonce keep each <= 1.
            bidIndexSuccessCount[keccak256(abi.encode(who, nonceKey, bidIndex))] += 1;
            quoteNonceSuccessCount[keccak256(abi.encode(operatorKeyId, q.nonce))] += 1;
            bidSuccesses += 1; // activates the strengthened afterInvariant liveness asserts
            committedByIntent += amount; // no-getter bucket: free->committed lock (over-estimate)

            // Record (maxBid, salt) for the assigned winning seq so the reveal action can open it.
            revealOf[lotId][auction.getLot(lotId).winnerSeq] = RevealData({maxBid: amount, salt: salt, set: true});
        } catch {}
    }

    /// @notice Re-drive the same (principal, nonceKey, bidIndex) and (operatorKeyId, quote.nonce) a second
    ///         time. A sequential nonce ladder and a one-shot quote nonce mean this must not succeed; the
    ///         success counters stay <= 1, asserted by invariant_NonceReplayMonotonicity.
    function replayBid(uint256 lotSeed, uint256 whoSeed, uint64 /*bidIndexSeed*/) external {
        uint256 lotId = _lot(lotSeed);
        address who = _pick(whoSeed);
        _noteLot(lotId);
        _before();

        uint256 key = keyOf[who];

        if (key != 0) {
            uint192 nonceKey = _nonceKeyOf(lotId, who);
            uint256 live = auction.nonces(who, nonceKey);
            // Re-drive an already-consumed index (live - 1) with a real sig + quote, so the call reaches the
            // keyed-nonce gate and is rejected there (InvalidAccountNonce) rather than at the signature. When
            // no bid has landed (live == 0) this is a fresh bid at index 0 (count 0 -> 1), still <= 1.
            uint64 staleIndex = live == 0 ? 0 : uint64(live - 1);
            uint128 amount = uint128(1 ether);
            bytes32 salt = keccak256(abi.encode("J-replay-salt", lotId, who, staleIndex));
            Ceiling memory c = Ceiling({
                principal: who,
                sessionId: sessionId,
                lotId: lotId,
                ceilingCommit: keccak256(abi.encode(amount, salt)),
                strategy: 0,
                deadline: uint64(block.timestamp + 1 days),
                maxBids: 64,
                nonceKey: nonceKey
            });
            bytes memory sig = _signCeiling(c, key);
            bytes32 qnonce = keccak256(abi.encode("J-replay-qn", quoteNonceCounter));
            quoteNonceCounter += 1;
            AttestationQuote memory q =
                _realQuote(c, lotId, amount, staleIndex, auction.getLot(lotId).highBid, qnonce);
            try auction.placeBid(c, lotId, who, staleIndex, amount, sig, operatorKeyId, q) {
                bidIndexSuccessCount[keccak256(abi.encode(who, nonceKey, staleIndex))] += 1;
                quoteNonceSuccessCount[keccak256(abi.encode(operatorKeyId, q.nonce))] += 1;
                bidSuccesses += 1;
                committedByIntent += amount;
                revealOf[lotId][auction.getLot(lotId).winnerSeq] = RevealData({maxBid: amount, salt: salt, set: true});
            } catch {}
        }

        _sync(lotId);
    }

    function hammerLot(uint256 lotSeed) external {
        uint256 lotId = _lot(lotSeed);
        _noteLot(lotId);
        _before();

        try auction.hammer(lotId) {} catch {}

        _sync(lotId);
    }

    /// @notice Open the winning commitment so finalizeWinner's reveal gate passes, unlocking the
    ///         Awaiting -> markDelivered -> confirm/release and openDispute pipeline. Reads the (maxBid,
    ///         salt) committed for the current winnerSeq and reveals as the winner. winnerSeq + winner are
    ///         read BEFORE vm.prank: an inline getLot after the prank consumes it, leaving reveal unpranked
    ///         (reverts NotPrincipal).
    function revealWinner(uint256 lotSeed) external {
        uint256 lotId = _lot(lotSeed);
        _noteLot(lotId);
        _before();

        Lot memory lot = auction.getLot(lotId);
        uint64 wseq = lot.winnerSeq;
        address winner = lot.highBidder;
        RevealData memory rd = revealOf[lotId][wseq];

        if (rd.set && winner != address(0)) {
            vm.prank(winner);
            try auction.reveal(lotId, wseq, rd.maxBid, rd.salt) {} catch {}
        }

        _sync(lotId);
    }

    function finalize(uint256 lotSeed) external {
        uint256 lotId = _lot(lotSeed);
        _noteLot(lotId);
        _before();

        // Gate-blocks-release: snapshot the gate + phase before the call and flag releasedWhileGateOpen iff
        // the lot advanced to Settled while the gate was open at the attempt. finalizeWinner targets
        // Awaiting (not Settled), so this leg trips only on a buggy finalize that jumps straight to Settled
        // through an open gate; the normal Settled drivers (confirm / releaseWindow / resolve) carry the
        // same snapshot.
        (bool gateWasOpen, uint8 prePhase, uint128 preEscrow) = _snapGate(lotId);

        try auction.finalizeWinner(lotId) {} catch {}

        _flagReleaseThroughGate(lotId, gateWasOpen, prePhase, preEscrow);
        _sync(lotId);
    }

    /// @notice markDelivered is onlySeller; prank the lot's seller so an Awaiting lot can reach Delivered
    ///         (the precondition for the buyer-silence releaseAfterWindow exit the no-strand liveness
    ///         path drives).
    function markDeliveredLot(uint256 lotSeed) external {
        uint256 lotId = _lot(lotSeed);
        _noteLot(lotId);
        _before();

        address theSeller = auction.getLot(lotId).seller;

        if (theSeller != address(0)) {
            vm.prank(theSeller);
        }

        try auction.markDelivered(lotId, keccak256("proof"), "cid") {} catch {}

        _sync(lotId);
    }

    /// @notice confirmReceipt is onlyBuyer; prank the recorded high bidder so a Delivered lot can be
    ///         confirmed (the buyer-driven release; the counterparty-independent release is
    ///         releaseAfterWindow, driven separately).
    function confirm(uint256 lotSeed) external {
        uint256 lotId = _lot(lotSeed);
        _noteLot(lotId);
        _before();

        address buyer = auction.getLot(lotId).highBidder;

        // Gate-blocks-release: confirmReceipt drives _release to Settled, so snapshot the gate + phase +
        // escrow at the attempt. Must run before vm.prank: _snapGate's getLot staticcall would consume the
        // prank and leave confirmReceipt running unpranked (failing onlyBuyer).
        (bool gateWasOpen, uint8 prePhase, uint128 preEscrow) = _snapGate(lotId);

        if (buyer != address(0)) {
            vm.prank(buyer);
        }

        try auction.confirmReceipt(lotId, keccak256("photo"), "cid") {} catch {}

        _flagReleaseThroughGate(lotId, gateWasOpen, prePhase, preEscrow);
        _sync(lotId);
    }

    /// @notice releaseAfterWindow is the buyer-silence counterparty-independent exit: permissionless,
    ///         anchored on the frozen deliveredAt + disputeWindowSec. Marks the independent-exit-attempted
    ///         ghost so the no-strand liveness check can assert a non-terminal Delivered lot, once warped
    ///         past its window, leaves the non-terminal set.
    function releaseWindow(uint256 lotSeed) external {
        uint256 lotId = _lot(lotSeed);
        _noteLot(lotId);
        _before();

        // Arm the independent-exit-attempted ghost only when releaseAfterWindow's exact precondition holds:
        // Delivered, past the frozen deliveredAt + disputeWindowSec, the Class B gate closed (it blocks
        // _release), and the session not voided (a void routes the exit through withdrawRefund). When all
        // hold, releaseAfterWindow must settle the lot, so a non-terminal result is a real strand.
        Lot memory lotR = auction.getLot(lotId);

        if (
            !sessionWasVoided && lotR.deliveryState == uint8(DeliveryState.Delivered)
                && block.timestamp >= uint256(lotR.deliveredAt) + DISPUTE_WINDOW_SEC
                && !auction.bidIntegrityDisputeOpen(lotId)
        ) {
            independentExitAttempted[lotId] = true;
        }

        // Gate-blocks-release: releaseAfterWindow drives _release to Settled.
        (bool gateWasOpen, uint8 prePhase, uint128 preEscrow) = _snapGate(lotId);

        try auction.releaseAfterWindow(lotId) {} catch {}

        _flagReleaseThroughGate(lotId, gateWasOpen, prePhase, preEscrow);
        _sync(lotId);
    }

    /// @notice reclaimUndelivered is the vanished-seller counterparty-independent exit: the buyer's
    ///         no-strand reclaim, anchored on the frozen awaitingAt + sellerDeliverSec. Marks the
    ///         independent-exit-attempted ghost (the prank satisfies the onlyBuyer gate).
    function reclaim(uint256 lotSeed) external {
        uint256 lotId = _lot(lotSeed);
        _noteLot(lotId);
        _before();

        // Arm the ghost only when reclaimUndelivered's exact precondition holds: AwaitingDelivery, past the
        // frozen awaitingAt + sellerDeliverSec, session not voided. reclaimUndelivered -> _refund is not
        // Class-B-gated. When this holds the reclaim must settle to Refunded; a non-terminal result is a
        // real vanished-seller strand.
        Lot memory lotR = auction.getLot(lotId);

        if (
            !sessionWasVoided && lotR.deliveryState == uint8(DeliveryState.AwaitingDelivery)
                && block.timestamp >= uint256(lotR.awaitingAt) + SELLER_DELIVER_SEC
        ) {
            independentExitAttempted[lotId] = true;
        }

        // reclaimUndelivered is onlyBuyer: prank the recorded high bidder so a real Awaiting lot can be
        // reclaimed.
        address buyer = auction.getLot(lotId).highBidder;

        if (buyer != address(0)) {
            vm.prank(buyer);
        }

        try auction.reclaimUndelivered(lotId) {} catch {}

        _sync(lotId);
    }

    function commitBook(uint256 lotSeed) external {
        uint256 lotId = _lot(lotSeed);
        _noteLot(lotId);
        _before();

        try auction.commitBidBook(lotId, keccak256("root")) {} catch {}

        _sync(lotId);
    }

    function voidLot(uint256 lotSeed, uint256 whoSeed) external {
        uint256 lotId = _lot(lotSeed);
        _noteLot(lotId);
        _before();

        // Empty promotion candidate (proofs would not verify); exercises the void-promote escrow-write
        // path the single-exit invariant cares about (the escrowAmount re-snapshot).
        NextCleanCandidate memory cand = NextCleanCandidate({
            heapIndex: 0,
            bidder: _pick(whoSeed),
            amount: 0,
            paddleId: 0,
            seq: 0,
            flagNonMembership: new bytes32[](0),
            precedingFlagInclusion: new bytes32[][](0)
        });
        bytes32[] memory proof = new bytes32[](0);

        try auction.voidAndAward(lotId, proof, cand) {} catch {}

        _sync(lotId);
    }

    /// @notice Class B bonded integrity challenge. Pulls the integrity bond into the clone, so on success
    ///         it is added to totalFundedIn and increments the per-lot Class B open count.
    function challengeAttest(uint256 lotSeed, uint64 seqSeed) external {
        uint256 lotId = _lot(lotSeed);
        uint64 seq = _seq(seqSeed);
        _noteLot(lotId);
        _before();

        if (nativeRail) {
            vm.deal(address(this), address(this).balance + INTEGRITY_BOND);
            try auction.challengeAttestation{value: INTEGRITY_BOND}(lotId, seq, "") {
                totalFundedIn += INTEGRITY_BOND;
                integrityBondByIntent += INTEGRITY_BOND; // no-getter bucket (the integrity-dispute bond)
                classBOpens[lotId] += 1;
            } catch {}
        } else {
            token.mint(address(this), INTEGRITY_BOND);
            token.approve(address(auction), INTEGRITY_BOND);
            try auction.challengeAttestation(lotId, seq, "") {
                totalFundedIn += INTEGRITY_BOND;
                integrityBondByIntent += INTEGRITY_BOND; // no-getter bucket (the integrity-dispute bond)
                classBOpens[lotId] += 1;
            } catch {}
        }

        _sync(lotId);
    }

    /// @notice Class A self-proving over-ceiling challenge. Records harm into the operator bond ledger and
    ///         never writes the IntegrityDispute record or flips lot.bidIntegrityOpen; successes are
    ///         counted only to assert that Class A never opens the gate.
    function challengeOverCeilingAction(uint256 lotSeed, uint64 seqSeed) external {
        uint256 lotId = _lot(lotSeed);
        uint64 seq = _seq(seqSeed);
        _noteLot(lotId);
        _before();

        try auction.challengeOverCeiling(lotId, seq, uint128(1 ether), keccak256("salt")) {
            classAActions[lotId] += 1;
        } catch {}

        _sync(lotId);
    }

    /// @notice Class B arbiter resolver. Decrements lot.bidIntegrityOpen on success. An upheld resolve
    ///         records a nonzero provenHarm so the fuzzer exercises the recordClaim accumulation path
    ///         (harm summed across distinct seqs) with real values; the harm lands in the operator bond
    ///         ledger (no auction-clone fund movement, so conservation is unaffected). The full close ->
    ///         settle -> claim payout is pinned by test_M1_VictimPaidSumOfMultiSeqHarmNotMax.
    function resolveIntegrity(uint256 lotSeed, uint64 seqSeed, bool upheld) external {
        uint256 lotId = _lot(lotSeed);
        uint64 seq = _seq(seqSeed);
        _noteLot(lotId);
        _before();

        // resolveBidIntegrityDispute is onlyArbiter; prank the arbiter so this can decrement the gate.
        vm.prank(arbiter());
        try auction.resolveBidIntegrityDispute(lotId, seq, upheld, uint128(1 ether)) {
            classBCloses[lotId] += 1;
        } catch {}

        _sync(lotId);
    }

    function timeoutIntegrity(uint256 lotSeed, uint64 seqSeed) external {
        uint256 lotId = _lot(lotSeed);
        uint64 seq = _seq(seqSeed);
        _noteLot(lotId);
        _before();

        try auction.timeoutBidIntegrityDispute(lotId, seq) {
            classBCloses[lotId] += 1;
        } catch {}

        _sync(lotId);
    }

    function voidWholeSession() external {
        _before();
        try auction.voidSession("invariant-void") {
            sessionWasVoided = true; // under a void the exits become withdrawRefund, not reclaim/release
        } catch {}
        // Re-sync every known lot's post-void escrow state into the ghosts. voidSession is pull-refund (it
        // typically moves no funds), but the sweep keeps conservation exact if it ever does.
        for (uint256 i = 0; i < touchedLots.length; i++) {
            _sync(touchedLots[i]);
        }
    }

    function dispute(uint256 lotSeed, uint256 whoSeed) external {
        uint256 lotId = _lot(lotSeed);
        address who = _pick(whoSeed);
        _noteLot(lotId);
        _before();

        if (nativeRail) {
            vm.deal(who, who.balance + DISPUTE_BOND);
            vm.prank(who);
            try auction.openDispute{value: DISPUTE_BOND}(lotId, keccak256("claim")) {
                totalFundedIn += DISPUTE_BOND;
                bondPulledIn += DISPUTE_BOND; // inflow from the openDispute pull, not a disputeBond delta
            } catch {}
        } else {
            token.mint(who, DISPUTE_BOND);
            vm.prank(who);
            token.approve(address(auction), DISPUTE_BOND);
            vm.prank(who);
            try auction.openDispute(lotId, keccak256("claim")) {
                totalFundedIn += DISPUTE_BOND;
                bondPulledIn += DISPUTE_BOND;
            } catch {}
        }

        _sync(lotId);
    }

    /// @notice Open a dispute as the lot's actual authorized party. openDispute is restricted to the lot's
    ///         buyer (highBidder) or seller (else Unauthorized), so this pranks whichever party `asSeller`
    ///         selects, making a real Disputed lot reachable for both opener identities. That lets
    ///         resolve()'s exact-recipient checks (winner gain == escrow-leg + bond, fee sink == fee leg)
    ///         and the dispute-bond closed-pool conservation (bondPulledIn == bondPaidOut + held) become
    ///         load-bearing once placeBid lands. The arbitrary-principal dispute() above almost always
    ///         fails Unauthorized (a random pick rarely equals the buyer, and the seller is not in the
    ///         principal set); it is kept to pin that fail-closed path. The pull is folded into
    ///         totalFundedIn + bondPulledIn exactly as dispute() does.
    function disputeAsParty(uint256 lotSeed, bool asSeller) external {
        uint256 lotId = _lot(lotSeed);
        _noteLot(lotId);
        _before();

        Lot memory lot = auction.getLot(lotId);
        address opener = asSeller ? lot.seller : lot.highBidder;

        if (opener == address(0)) {
            _sync(lotId); // no winner / no seller yet; keep ghosts coherent
            return;
        }

        if (nativeRail) {
            vm.deal(opener, opener.balance + DISPUTE_BOND);
            vm.prank(opener);
            try auction.openDispute{value: DISPUTE_BOND}(lotId, keccak256("claim-party")) {
                totalFundedIn += DISPUTE_BOND;
                bondPulledIn += DISPUTE_BOND; // inflow from the pull intent, identical to dispute()
            } catch {}
        } else {
            token.mint(opener, DISPUTE_BOND);
            vm.prank(opener);
            token.approve(address(auction), DISPUTE_BOND);
            vm.prank(opener);
            try auction.openDispute(lotId, keccak256("claim-party")) {
                totalFundedIn += DISPUTE_BOND;
                bondPulledIn += DISPUTE_BOND;
            } catch {}
        }

        _sync(lotId);
    }

    function resolve(uint256 lotSeed, bool toSeller) external {
        uint256 lotId = _lot(lotSeed);
        _noteLot(lotId);
        _before();
        Resolution res = toSeller ? Resolution.ReleaseToSeller : Resolution.RefundToBuyer;

        // Recipient correctness: the bond must reach exactly the winning party. Snapshot the bond held, the
        // winner/loser, and their claimable (pendingWithdrawal + rail balance) before the resolution. The
        // winning party is the seller (ReleaseToSeller) or the buyer (RefundToBuyer); the winner gets escrow
        // and bond, the loser gets nothing.
        Lot memory pre = auction.getLot(lotId);
        uint96 bondHeld = pre.disputeBond;
        uint128 escrowPre = pre.escrowAmount;
        address winner = toSeller ? pre.seller : pre.highBidder;
        address loser = toSeller ? pre.highBidder : pre.seller;
        uint256 winnerClaimablePre = _claimable(winner);
        uint256 loserClaimablePre = _claimable(loser);

        // Gate-blocks-release: resolveDispute(ReleaseToSeller) drives _release to Settled, so snapshot the
        // gate at the attempt (pre-phase + pre-escrow come from `pre` above). The RefundToBuyer branch goes
        // to Refunded, not Settled, and the gate blocks _release not _refund, so this is only armed for the
        // release leg (below).
        bool gateWasOpen = auction.bidIntegrityDisputeOpen(lotId);
        uint8 prePhase = pre.phase;

        // Exact escrow leg the winner is owed besides the bond: under RefundToBuyer _refund pushes the full
        // escrow to the buyer; under ReleaseToSeller _release pays the seller escrow - fee, where
        // fee = Math.mulDiv(escrow, FEE_BPS, 10_000), and pays the same fee to _feeRecipient in the same
        // call. The winner's claimable must rise by exactly (escrow leg + bond): a bond split or redirected
        // to any third address breaks the equality even though the escrow leg satisfies the >= bond bound.
        uint256 feeLeg = toSeller ? Math.mulDiv(uint256(escrowPre), FEE_BPS, 10_000) : 0;
        uint256 expectedEscrowToWinner = toSeller ? uint256(escrowPre) - feeLeg : uint256(escrowPre);

        // Snapshot the fee sink: under ReleaseToSeller it must rise by exactly the fee (a bond leaked into
        // it would push it to fee + bond); under RefundToBuyer _release never runs so it must not move. The
        // fee sink is structurally disjoint from winner and loser.
        address feeSink = feeRecipient();
        uint256 feeSinkPre = _claimable(feeSink);

        // resolveDispute is onlyArbiter; prank the arbiter so the bond payout is observed by the J-03
        // disputeBond zero-transition.
        vm.prank(arbiter());
        try auction.resolveDispute(lotId, res, keccak256("photo")) {
            // Only meaningful when a bond was actually held and paid out (disputeBond zeroed).
            Lot memory post = auction.getLot(lotId);
            if (bondHeld != 0 && post.disputeBond == 0) {
                // (1) The winner gained at least the bond (it also gains escrow, so gained >= bondHeld).
                // Can still pass when escrow masks a misrouted bond, which is why (2)/(3) are sharper.
                if (winner != address(0) && _claimable(winner) - winnerClaimablePre < bondHeld) {
                    bondToWrongParty[lotId] = true;
                }
                // (2) The loser gets nothing (no escrow flow to mask a leaked bond), so its claimable must
                // not rise. A bond misrouted or split to the loser trips here.
                if (loser != address(0) && loser != winner && _claimable(loser) > loserClaimablePre) {
                    bondToWrongParty[lotId] = true;
                }
                // (3) Exact winner delta: claimable must rise by exactly expectedEscrowToWinner + bondHeld.
                // A bond redirected to a third party (fee sink / arbiter / attacker) leaves the winner's gain
                // at the escrow leg, below this target, so it trips here where (1) and (2) pass. Scoped to
                // winner disjoint from feeSink/loser so an overlapping recipient cannot perturb the equality.
                if (winner != address(0) && winner != feeSink && winner != loser) {
                    if (_claimable(winner) - winnerClaimablePre != expectedEscrowToWinner + uint256(bondHeld)) {
                        bondNotExactToWinner[lotId] = true;
                    }
                }
                // (4) Exact fee-sink delta: under ReleaseToSeller the fee sink rises by exactly feeLeg (a
                // bond leaked into it would push it to feeLeg + bond); under RefundToBuyer it must not move.
                if (feeSink != winner && feeSink != loser) {
                    if (_claimable(feeSink) - feeSinkPre != feeLeg) {
                        bondNotExactToWinner[lotId] = true;
                    }
                }
            }
        } catch {}

        // Arm the gate-blocks-release check only on the release leg (toSeller): RefundToBuyer zeroes escrow
        // via _refund, which the gate does not block, so a legitimate RefundToBuyer through an open gate
        // must not trip the fund coupling. The phase coupling is already self-scoping (RefundToBuyer goes to
        // Refunded), but the fund coupling needs this explicit leg scoping.
        _flagReleaseThroughGate(lotId, gateWasOpen && toSeller, prePhase, escrowPre);

        _sync(lotId);
    }

    /// @dev Total claimable for an account on the active rail: failed-push pending credit plus spendable
    ///      rail balance (native ETH or token). The bond may arrive as a direct _pay or, on push failure,
    ///      as a pending credit; either way it lands in this sum, so this detects which party it reached.
    function _claimable(address who) internal view returns (uint256) {
        uint256 pending = auction.pendingWithdrawal(who);
        return pending + (nativeRail ? who.balance : token.balanceOf(who));
    }

    /// @notice withdrawRefund is the universal pull exit: step 1 returns free + committed, step 2 returns
    ///         the winner's escrow under a session void, step 3 returns a Disputed lot's disputeBond to the
    ///         opener when resolveDispute can no longer fire (the vanished-arbiter counterparty-independent
    ///         exit).
    function refundUnderVoid(uint256 lotSeed, uint256 whoSeed) external {
        uint256 lotId = _lot(lotSeed);
        address who = _pick(whoSeed);
        _noteLot(lotId);
        _before();

        // This is the conditional exit (step 3, vanished-arbiter under a prior void), not the unconditional
        // single-step exit invariant_NonTerminalHasIndependentExit asserts, so it must not arm
        // independentExitAttempted (that would false-flag a strand when withdrawRefund cannot yet fire). The
        // endsAt-independence of this exit is pinned by test_NoStrand_WithdrawRefundNotAnchoredOnEndsAt.
        vm.prank(who);
        try auction.withdrawRefund(lotId) {} catch {}

        _sync(lotId);
    }

    /// @notice claimPending drains the caller's failed-push credit; the outflow is folded into
    ///         totalPaidOut so the pending-withdrawal exit path is visible to conservation.
    function claimPending(uint256 whoSeed) external {
        address who = _pick(whoSeed);
        _before();

        vm.prank(who);
        try auction.claimPending() {
            // On success the caller's pending credit must be fully drained (zeroed then paid).
            require(auction.pendingWithdrawal(who) == 0, "claimPending did not zero pending");
        } catch {}

        // No specific lot: fold the outflow into the ghost via a balance re-read.
        uint256 post = _cloneBalance();

        if (post < preCloneBal) {
            totalPaidOut += (preCloneBal - post);
        }
    }

    /// @notice Advance the clock past the longest frozen delivery-phase exit window so the
    ///         counterparty-independent exits (releaseAfterWindow, reclaimUndelivered, the integrity
    ///         timeout) become reachable and the no-strand liveness check can fire. Bounded under the
    ///         session end (setUp + 30 days; longest window is sellerDeliverSec == 7 days). Marks every
    ///         known lot resting non-terminal so liveness can require its escape after the warp. The warp
    ///         persists across the run.
    function warpPastWindow() external {
        // 8 days clears both the 7-day seller-deliver and 3-day dispute windows in one step.
        vm.warp(block.timestamp + 8 days);

        for (uint256 i = 0; i < touchedLots.length; i++) {
            uint256 lotId = touchedLots[i];
            uint8 ds = auction.getLot(lotId).deliveryState;

            if (
                ds == uint8(DeliveryState.AwaitingDelivery) || ds == uint8(DeliveryState.Delivered)
                    || ds == uint8(DeliveryState.Disputed)
            ) {
                warpedPastWindow[lotId] = true;
            }
        }
    }

    /// @notice Rotate the reentrant adversary's re-entry target across the run, so every seller-paying exit
    ///         is probed for a missing nonReentrant, not just withdrawDeposit. The fuzzer picks one of the
    ///         five parameterized exits and a lot; on any later native escrow/bond push to the attacker (a
    ///         registered principal) its receive() re-enters that exit. A double-fire from any rotated exit
    ///         breaks conservation and single-exit. No-op until the attacker is wired (setAttacker) and on
    ///         the ERC-20 rail (trySafeTransfer hands no callback).
    function rearmAttacker(uint256 lotSeed, uint8 modeSeed) external {
        if (address(reentrantAttacker) == address(0)) return;

        uint256 lotId = _lot(lotSeed);

        // 5 modes (WithdrawDeposit .. WithdrawRefund); generous re-entry amount so a buggy exit missing the
        // guard would actually move funds during the push window.
        FundReentrantRecipient.ReenterMode m = FundReentrantRecipient.ReenterMode(modeSeed % 5);
        reentrantAttacker.armMode(ISessionAuction(address(auction)), m, lotId, type(uint128).max);
    }

    // Views for the invariants.

    function touchedLotsLength() external view returns (uint256) {
        return touchedLots.length;
    }

    function touchedLotAt(uint256 i) external view returns (uint256) {
        return touchedLots[i];
    }

    function principalsLength() external view returns (uint256) {
        return principals.length;
    }

    function principalAt(uint256 i) external view returns (address) {
        return principals[i];
    }

    function cloneBalance() external view returns (uint256) {
        return _cloneBalance();
    }

    // The arbiter address, recomputed (makeAddr(name) == vm.addr(uint(keccak(name)))) so the handler can
    // prank it for resolveDispute / resolveBidIntegrityDispute without a constructor arg.
    function arbiter() internal view returns (address) {
        return vm.addr(uint256(keccak256(bytes("arbiter"))));
    }

    // The house fee recipient (HammerBase houseFeeRecipient), recomputed so resolve() can snapshot the fee
    // sink and assert the exact fee leg. It is structurally disjoint from the seller-winner and the
    // bidder-buyer, so a bond misrouted to it is invisible to the winner/loser delta checks.
    function feeRecipient() internal view returns (address) {
        return vm.addr(uint256(keccak256(bytes("houseFeeRecipient"))));
    }

    // Local copy of forge-std bound (the handler is a plain contract, not a Test); keeps calldata in a sane
    // range so the fuzzer spends its budget on state interleavings, not overflow noise.
    function bound(uint256 x, uint256 min, uint256 max) internal pure returns (uint256) {
        require(max >= min, "bound");
        uint256 size = max - min + 1;
        if (max == type(uint256).max && min == 0) return x;
        return min + (x % size);
    }
}

// FundInvariantsBase: the shared HammerBase-derived invariant harness. Wires the FundInvariantsHandler
// over an initialized clone on the rail the concrete subclass selects (native via FundInvariantsTest,
// ERC-20 via FundInvariantsErc20Test) and runs the same fund-safety properties against both rails. The
// abstract base owns every invariant_/test_; the concretes only pick the rail.
abstract contract FundInvariantsBase is HammerBase {
    FundInvariantsHandler internal handler;
    // Adversarial reentrant recipient: registered as a handler principal on both rails so any escrow/bond
    // push to it re-enters a withdraw/claim during the gas-capped native _pay. A reentrant double-pay
    // would break J-01 and J-02 automatically; test_ReentrantWithdrawCannotDoublePay pins it explicitly.
    FundReentrantRecipient internal attacker;

    // Treasury / OperatorBond pool balances snapshotted at setUp so the three-pool separation check can
    // assert neither pool ever absorbs the clone's bidder principal.
    uint256 internal treasuryBaselineEth;
    uint256 internal operatorBondBaselineEth;
    uint256 internal treasuryBaselineToken;
    uint256 internal operatorBondBaselineToken;

    // Rail hooks (overridden per concrete).
    function _nativeRail() internal pure virtual returns (bool);

    function _paymentToken() internal view virtual returns (address);

    /// @dev Rail-aware clone balance the invariants compare against the handler's funded-in/paid-out
    ///      ghost. Native reads address(auction).balance; ERC-20 reads token.balanceOf(clone).
    function _railCloneBalance() internal view returns (uint256) {
        return _nativeRail() ? address(auction).balance : token.balanceOf(address(auction));
    }

    function setUp() public virtual override {
        super.setUp();

        // Initialize the session clone on the selected rail.
        InitConfig memory cfg = _defaultInitConfig(_paymentToken());
        auction.initialize(cfg);

        // Open lots 1 and 2 as the hammer (openLot is onlyHammer). Lot 0 is left pristine for
        // test_StorageLayoutBaseline (which zero-reads it). The handler's _lot(seed)%3 deposits to {0,1,2}:
        // lots 1,2 land (depositSuccesses>0, conservation runs over real funded state); a lot-0 deposit
        // reverts NotOpen and is swallowed. Lot 1 gets a short window (the seeded-lifecycle lot below, a
        // small warp reaches its end to hammer it); lot 2 gets a long window so it stays biddable for the
        // fuzzer after the seed's warps (the live bid lot).
        vm.prank(address(hammer));
        auction.openLot(1, seller, RESERVE_PRICE, uint64(block.timestamp + 1 hours));
        vm.prank(address(hammer));
        auction.openLot(2, seller, RESERVE_PRICE, uint64(block.timestamp + 20 days));

        // The adversarial reentrant recipient: its receive()/fallback re-enters a withdraw/claim during any
        // native push. Pointed at the live clone so its re-entry hits the real nonReentrant guard.
        attacker = new FundReentrantRecipient(auction);

        // Four principals: three honest bidders plus the reentrant recipient. The recipient is in the set so
        // escrow/bond pushes can target it and its re-entry fires inside the gas-capped _pay; its
        // pendingWithdrawal is folded into the conservation getter cross-check and sweep.
        address[] memory ps = new address[](4);
        ps[0] = bidder1;
        ps[1] = bidder2;
        ps[2] = bidder3;
        ps[3] = address(attacker);

        // Per-principal ECDSA signing keys so the handler can sign a ceiling that recovers to the bidder.
        // makeAddrAndKey(name) returns the same address makeAddr(name) seeded for the three EOA bidders,
        // plus its key. The attacker is a contract (no key, 0): it cannot sign, so it never bids.
        uint256[] memory keys = new uint256[](4);
        (, keys[0]) = makeAddrAndKey("bidder1");
        (, keys[1]) = makeAddrAndKey("bidder2");
        (, keys[2]) = makeAddrAndKey("bidder3");
        keys[3] = 0;

        // KYC: register a nonzero paddle for each EOA bidder so placeBid's paddleOf gate passes.
        paddles.register(bidder1);
        paddles.register(bidder2);
        paddles.register(bidder3);

        // Thread the attestation kit into the handler (operator P-256 key + per-bidder ECDSA keys + the
        // pinned session/measurement) so its placeBid builds a passing ceiling sig + operator quote and the
        // fuzzer lands bids.
        handler = new FundInvariantsHandler(
            auction, token, _nativeRail(), ps, keys, operatorPkBase, opKeyIdBase, SESSION_ID, MR_ENCLAVE, VENDOR_ROOT
        );
        // Wire the attacker so rearmAttacker can rotate which exit it re-enters across the run.
        handler.setAttacker(attacker);

        // Seed the handler with native funds so its deposit/openDispute/challenge actions have value to move
        // on the native rail (the ERC-20 rail mints inside each action).
        vm.deal(address(handler), INITIAL_ETH);
        // Fund the attacker on both rails so its deposits/withdraws move real value and its re-entry has
        // standing balance to attempt a double-pull.
        vm.deal(address(attacker), INITIAL_ETH);
        token.mint(address(attacker), INITIAL_TOKEN);
        // Arm the attacker for the run: every native escrow/bond push re-enters withdrawDeposit(lot 0). The
        // gas-capped push + nonReentrant guard means it cannot double-pay; the generous amount maximizes the
        // chance a buggy impl would re-pay during the push window.
        attacker.arm(ISessionAuction(address(auction)), 0, type(uint128).max);

        // Seed funded deposits directly so the conservation / single-exit / reentrancy invariants run over
        // non-empty funded state from call 0 and the depositSuccesses liveness gate is met. The fuzzer
        // reverts handler state to this post-setUp snapshot between runs, so an in-run deposit never
        // survives to afterInvariant; the funds and the liveness counter must live in the snapshot. Seed
        // across both lots and the attacker so a later withdraw pushes native value and the adversary fires.
        handler.deposit(1, 0, uint128(10 ether)); // lot 1 <- bidder1
        handler.deposit(2, 1, uint128(10 ether)); // lot 2 <- bidder2
        handler.deposit(4, 3, uint128(10 ether)); // lot 1 <- attacker principal (re-entry standing)

        // Seed the full bid -> hammer -> challenge -> claim/settle lifecycle on lot 1, baking every
        // afterInvariant liveness floor into the snapshot (bidSuccesses, escrowZeroings, classB open+close,
        // dispute bond moved), since in-run successes do not survive the reset. The fuzzer then explores
        // safety from this state, principally on lot 2. Each step goes through a handler action so the
        // conservation ghosts stay authoritative; a step that cannot fire is swallowed by its try/catch.
        handler.placeBid(1, 0, uint128(6 ether), 0); // lot 1 <- bidder1: real attestation, lands (highBid 6e18)
        handler.challengeAttest(1, 1); // open a Class B dispute on seq 1 (classBOpens++)
        handler.resolveIntegrity(1, 1, false); // arbiter rejects -> gate closes (classBCloses++), bond to seller
        vm.warp(uint256(auction.getLot(1).endsAt)); // reach lot 1's (short) end so hammer is allowed
        handler.hammerLot(1); // -> Hammered, escrow == 6e18 set
        handler.revealWinner(1); // open the winning commit (satisfies the reveal gate)
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1); // close the after-commit challenge window
        handler.finalize(1); // -> Awaiting
        handler.markDeliveredLot(1); // seller marks delivered -> Delivered
        handler.disputeAsParty(1, true); // seller opens a delivery dispute (bondPulledIn++)
        handler.resolve(1, true); // ReleaseToSeller -> escrow exits (escrowZeroings++), bond paid (bondPaidOut++)

        // Baselines for the disjoint-pool assertion: neither Treasury nor OperatorBond may absorb the
        // clone's bidder principal (the only clone -> Treasury edge is a forfeit depositForfeit; there is
        // no clone -> OperatorBond fund edge for a bidder principal).
        treasuryBaselineEth = address(treasury).balance;
        operatorBondBaselineEth = address(operatorBond).balance;
        treasuryBaselineToken = token.balanceOf(address(treasury));
        operatorBondBaselineToken = token.balanceOf(address(operatorBond));

        // Target only the handler so the fuzzer drives the protocol through the wrapped, revert-swallowing
        // entrypoints, never the raw clone.
        targetContract(address(handler));

        bytes4[] memory sels = new bytes4[](30);
        sels[0] = handler.deposit.selector;
        sels[1] = handler.withdraw.selector;
        sels[2] = handler.placeBid.selector;
        sels[3] = handler.hammerLot.selector;
        sels[4] = handler.finalize.selector;
        sels[5] = handler.markDeliveredLot.selector;
        sels[6] = handler.confirm.selector;
        sels[7] = handler.releaseWindow.selector;
        sels[8] = handler.reclaim.selector;
        sels[9] = handler.dispute.selector;
        sels[10] = handler.resolve.selector;
        sels[11] = handler.refundUnderVoid.selector;
        sels[12] = handler.claimPending.selector;
        sels[13] = handler.commitBook.selector;
        sels[14] = handler.voidLot.selector;
        sels[15] = handler.challengeAttest.selector;
        sels[16] = handler.timeoutIntegrity.selector;
        sels[17] = handler.voidWholeSession.selector;
        sels[18] = handler.placeBid.selector; // weight the bid path more heavily
        sels[19] = handler.challengeOverCeilingAction.selector; // Class A driver
        sels[20] = handler.resolveIntegrity.selector; // Class B resolver
        sels[21] = handler.replayBid.selector; // nonce / quote replay re-drive
        sels[22] = handler.challengeAttest.selector; // weight the Class B open path so the gate exercises
        sels[23] = handler.warpPastWindow.selector; // advance past frozen delivery windows (liveness)
        sels[24] = handler.rearmAttacker.selector; // rotate the reentrant adversary across every exit
        sels[25] = handler.disputeAsParty.selector; // open a real dispute as the buyer/seller
        sels[26] = handler.disputeAsParty.selector; // weight the real-party dispute so Disputed lots are reached
        sels[27] = handler.revealWinner.selector; // open the winning commit so finalize -> dispute -> release unlocks
        sels[28] = handler.placeBid.selector; // extra bid weight (denser escrow / Class B state)
        sels[29] = handler.revealWinner.selector; // weight reveal so the finalize / delivery pipeline is reached
        targetSelector(FuzzSelector({addr: address(handler), selectors: sels}));
    }

    /// Deterministic proof that the handler drives the full bid -> hammer -> challenge -> finalize ->
    /// dispute -> settle lifecycle. (1) Asserts the setUp seed baked every afterInvariant liveness floor
    /// into the snapshot on lot 1. (2) Re-drives lot 2 (open, long window, bidder2 funded in setUp) through
    /// a different escrow exit (buyer confirmReceipt) to pin the path repeatable + rail-honest.
    function test_HandlerDrivesFullLifecycle() public {
        // (1) The setUp seed must have moved every subject the bidSuccesses>0 afterInvariant floors gate on.
        assertGt(handler.bidSuccesses(), 0, "seed: no bid ever landed");
        assertEq(handler.escrowZeroings(1), 1, "seed: lot1 escrow did not exit exactly once");
        assertGt(handler.classBOpens(1), 0, "seed: Class B gate never opened");
        assertGt(handler.classBCloses(1), 0, "seed: Class B gate never closed");
        assertGt(handler.bondPulledIn() + handler.bondPaidOut(), 0, "seed: no D5 dispute bond ever moved");
        assertEq(uint256(auction.getLot(1).phase), uint256(LotPhase.Settled), "seed: lot1 not Settled");
        assertEq(auction.getLot(1).escrowAmount, 0, "seed: lot1 escrow not zeroed at Settled");

        // (2) Re-drive lot 2 end to end via the buyer-confirm release (the seed used dispute->resolve).
        handler.placeBid(2, 1, uint128(5 ether), 0); // lot 2 <- bidder2
        assertEq(auction.getLot(2).highBidder, bidder2, "lot2 bid did not land");
        vm.warp(uint256(auction.getLot(2).endsAt));
        handler.hammerLot(2);
        assertEq(uint256(auction.getLot(2).phase), uint256(LotPhase.Hammered), "lot2 not Hammered");
        handler.revealWinner(2);
        assertTrue(auction.getLot(2).revealed, "lot2 winner did not reveal");
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        handler.finalize(2);
        assertEq(uint256(auction.getLot(2).phase), uint256(LotPhase.Awaiting), "lot2 not Awaiting");
        handler.markDeliveredLot(2);
        handler.confirm(2); // buyer confirms receipt -> _release -> Settled, escrow exits
        assertEq(uint256(auction.getLot(2).phase), uint256(LotPhase.Settled), "lot2 not Settled via confirm");
        assertEq(handler.escrowZeroings(2), 1, "lot2 escrow did not exit exactly once");
    }

    /// Contract-safety pin behind invariant_ClassBGateMonotonicity: finalizeWinner (and _release) revert
    /// BidIntegrityDisputeIsOpen while a Class B gate is open; the lot advances only after the gate clears
    /// (here via the permissionless integrity timeout). No release advances through an open gate, so the
    /// gate-blocks-release detector stays silent.
    function test_ClassBGateBlocksRelease() public {
        handler.placeBid(2, 1, uint128(5 ether), 0);
        vm.warp(uint256(auction.getLot(2).endsAt));
        handler.hammerLot(2);
        handler.revealWinner(2);
        handler.challengeAttest(2, 1); // open a Class B dispute on seq 1 before finalize
        assertTrue(auction.bidIntegrityDisputeOpen(2), "Class B gate open");
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        handler.finalize(2); // blocked by the open gate -> stays Hammered
        assertEq(uint256(auction.getLot(2).phase), uint256(LotPhase.Hammered), "finalize blocked by open Class B gate");
        assertFalse(handler.releasedWhileGateOpen(2), "no release advanced through the gate (detector A silent)");
        // The gate clears via the permissionless integrity timeout, then finalize proceeds.
        vm.warp(block.timestamp + INTEGRITY_TIMEOUT_SEC + 1);
        handler.timeoutIntegrity(2, 1);
        assertFalse(auction.bidIntegrityDisputeOpen(2), "gate cleared by timeout");
        handler.finalize(2);
        assertEq(uint256(auction.getLot(2).phase), uint256(LotPhase.Awaiting), "finalize proceeds once gate clears");
    }

    /// A Class B dispute opened on an already-settled lot (challengeAttestation gates only on the integrity
    /// window + seq existence, not the lot phase) is benign: the escrow released earlier with the gate
    /// closed, so this is a pure operator-slash record. It must NOT flag a release-through-gate (the case an
    /// at-sync detector would false-positive on).
    function test_PostSettleClassBDoesNotFalseTripGateDetector() public {
        handler.placeBid(2, 1, uint128(5 ether), 0);
        vm.warp(uint256(auction.getLot(2).endsAt));
        handler.hammerLot(2);
        handler.revealWinner(2);
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        handler.finalize(2);
        handler.markDeliveredLot(2);
        handler.confirm(2);
        assertEq(uint256(auction.getLot(2).phase), uint256(LotPhase.Settled), "lot2 Settled");
        assertFalse(handler.releasedWhileGateOpen(2), "no release through an open gate at settle");
        handler.challengeAttest(2, 1); // Class B on the settled lot's seq 1 (allowed; benign)
        assertTrue(auction.bidIntegrityDisputeOpen(2), "Class B opened post-settle");
        assertFalse(handler.releasedWhileGateOpen(2), "post-settle Class B must NOT flag a release-through-gate");
    }

    /// Pin behind invariant_NonTerminalHasIndependentExit: a Delivered lot with an open Class B gate has
    /// releaseAfterWindow blocked (the gate blocks _release), but the counterparty-independent exit still
    /// exists as two permissionless steps (timeoutBidIntegrityDispute then releaseAfterWindow), so the lot
    /// is not stranded.
    function test_ClassBGateDoesNotStrandDeliveredLot() public {
        handler.placeBid(2, 1, uint128(5 ether), 0);
        vm.warp(uint256(auction.getLot(2).endsAt));
        handler.hammerLot(2);
        handler.revealWinner(2);
        vm.warp(block.timestamp + AC_CHALLENGE_SEC + 1);
        handler.finalize(2);
        handler.markDeliveredLot(2);
        handler.challengeAttest(2, 1); // open Class B after delivery
        vm.warp(block.timestamp + DISPUTE_WINDOW_SEC + 1);
        handler.releaseWindow(2); // releaseAfterWindow blocked by the open gate -> stays Delivered
        assertTrue(uint256(auction.getLot(2).phase) != uint256(LotPhase.Settled), "release blocked by open gate");
        // The exit exists: clear the gate via the permissionless integrity timeout, then release succeeds.
        vm.warp(block.timestamp + INTEGRITY_TIMEOUT_SEC + 1);
        handler.timeoutIntegrity(2, 1);
        handler.releaseWindow(2);
        assertEq(uint256(auction.getLot(2).phase), uint256(LotPhase.Settled), "two-step exit reaches terminal");
    }

    /// End-to-end through the full claim path: a single victim harmed at two distinct seqs is paid the SUM
    /// of the proven harm, not the max. bidder1 self-outbids (seq 1, then seq 2), both seqs are Class B
    /// challenged and arbiter-upheld with distinct harms (3e18, 2e18), recordClaim sums to 5e18, the session
    /// is sealed + settled (pool covers the claims), and claimSlash pays bidder1 the sum.
    function test_M1_VictimPaidSumOfMultiSeqHarmNotMax() public {
        uint128 harm1 = 3 ether;
        uint128 harm2 = 2 ether;
        uint256 stake = 20 ether; // pool >= totalClaims (5e18) so the victim is paid the FULL summed harm

        // bidder1 funds lot 2 and self-outbids -> seq 1 and seq 2, both with principal == bidder1.
        handler.deposit(2, 0, uint128(40 ether)); // bidder1 large free on lot 2
        handler.placeBid(2, 0, uint128(0), 0); // seq 1 at the reserve floor (amountSeed 0 -> range min)
        handler.placeBid(2, 0, uint128(5 ether), 0); // seq 2 strictly higher (self-outbid)
        assertEq(uint256(auction.getLot(2).winnerSeq), 2, "expected two bidder1 seqs (1 then 2)");
        assertEq(auction.getLot(2).highBidder, bidder1, "bidder1 is the top after self-outbid");

        // An operator stakes the session bond pool (rail-aware).
        if (_nativeRail()) {
            vm.deal(operator1, operator1.balance + stake);
            vm.prank(operator1);
            operatorBond.deposit{value: stake}(SESSION_ID, address(auction), stake);
        } else {
            token.mint(operator1, stake);
            vm.prank(operator1);
            token.approve(address(operatorBond), stake);
            vm.prank(operator1);
            operatorBond.deposit(SESSION_ID, address(auction), stake);
        }

        // Class B challenge BOTH seqs (handler is the challenger), then the arbiter upholds BOTH with
        // DISTINCT harms against bidder1 -> recordClaim sums 3e18 + 2e18 into _harmOf[bidder1].
        handler.challengeAttest(2, 1);
        handler.challengeAttest(2, 2);
        vm.prank(arbiter);
        auction.resolveBidIntegrityDispute(2, 1, true, harm1);
        vm.prank(arbiter);
        auction.resolveBidIntegrityDispute(2, 2, true, harm2);

        // Seal the claim ledger after the bond-claims window, settle the pool, then the victim pulls.
        vm.warp(auction.bondClaimsCloseAt() + 1);
        operatorBond.closeSession(SESSION_ID, address(auction));
        operatorBond.settleSlash(SESSION_ID);

        uint256 pre = _railBalOf(bidder1);
        vm.prank(bidder1);
        operatorBond.claimSlash(SESSION_ID);
        uint256 got = _railBalOf(bidder1) - pre;
        assertEq(got, uint256(harm1) + uint256(harm2), "M1: victim must be paid the SUM of multi-seq harm, not the max");
    }

    /// @dev Rail-aware spendable balance of an account (native ETH or the session token).
    function _railBalOf(address who) internal view returns (uint256) {
        return _nativeRail() ? who.balance : token.balanceOf(who);
    }

    // Shared getter cross-check.

    /// @notice Sum only the fund buckets the surface exposes a getter for: escrowAmount, disputeBond (per
    ///         lot), withdrawableFree (per principal, the free term of Deposit), and pendingWithdrawal (per
    ///         account). The two no-getter buckets (the locked committed term of Deposit, and
    ///         _integrityDispute.bond) are excluded, so this is a lower bound on what the clone holds, never
    ///         an equality target.
    function _getterBucketSum() private view returns (uint256 sum) {
        uint256 nLots = handler.touchedLotsLength();
        uint256 nPrincipals = handler.principalsLength();

        for (uint256 i = 0; i < nLots; i++) {
            uint256 lotId = handler.touchedLotAt(i);
            Lot memory lot = auction.getLot(lotId);
            sum += lot.escrowAmount; // bucket: winner escrow still held
            sum += lot.disputeBond; // bucket: delivery dispute bond still held
            for (uint256 j = 0; j < nPrincipals; j++) {
                sum += auction.withdrawableFree(lotId, handler.principalAt(j)); // free term only
            }
        }

        sum += auction.pendingWithdrawal(seller);
        sum += auction.pendingWithdrawal(address(handler));

        for (uint256 j = 0; j < nPrincipals; j++) {
            sum += auction.pendingWithdrawal(handler.principalAt(j));
        }
    }

    /// J-01 (invariant_FundConservation): the clone's payment-token balance equals the handler's own
    /// cumulative accounting (funded-in minus paid-out) after every randomized call, on both rails. This
    /// identity needs neither the committed getter nor the integrity-bond getter the surface omits, so it
    /// is structurally complete and rail-agnostic. The getter-bucket sum is kept as a <= cross-check, and
    /// the Treasury / OperatorBond pools must never drift (three-pool separation). Holds across reverted
    /// (fail-closed) calls because a reverted call moves nothing.
    function invariant_FundConservation() public view {
        uint256 cloneBal = _railCloneBalance();
        uint256 fundedIn = handler.totalFundedIn();
        uint256 paidOut = handler.totalPaidOut();

        // Every unit the clone holds was funded in and not yet paid out: no path mints (cloneBal > fundedIn
        // - paidOut) and no path strands value outside accounting (cloneBal short). Stated additively to
        // avoid subtraction underflow, plus an explicit paidOut <= fundedIn mint check.
        assertLe(paidOut, fundedIn, "J-01: paid out more than funded in (mint on a push path)");
        assertEq(cloneBal + paidOut, fundedIn, "J-01: cloneBalance + paidOut != fundedIn");

        // Getter cross-check, upper bound: the getter buckets cannot exceed the held balance (the unread
        // committed + integrity-bond buckets make up any remainder). A getter sum above the balance would
        // mean a bucket double-counts held funds.
        uint256 getterSum = _getterBucketSum();
        assertLe(getterSum, cloneBal, "J-01: getter buckets exceed clone balance");

        // Getter cross-check, lower bound: the only legitimately-unreadable held terms are committed + the
        // integrity bond, both tracked by intent, so getterSum plus those intents must be at least the clone
        // balance. A getterSum below (cloneBal - knownUnreadable) means held funds went somewhere neither a
        // getter nor the no-getter buckets explain (a strand or mis-rebalance). The intents are monotonic
        // over-estimates of the held unreadable balance, safe for a >= bound and exact (0) under the frozen
        // fixture.
        assertGe(
            getterSum + handler.committedByIntent() + handler.integrityBondByIntent(),
            cloneBal,
            "J-01: getter buckets + known-unreadable intent fall short of clone balance (strand / mis-rebalance)"
        );

        // Three-pool separation, forfeit-aware. The one legal clone -> Treasury move (the depositForfeit
        // outflow) is already netted into totalPaidOut, so a strict baseline equality would false-fail once
        // voidAndAward is reachable. Instead bound the sink-pool growth: the bidder-escrow pool (this
        // clone), OperatorBond, and the Treasury forfeit pool stay disjoint in that no bidder principal is
        // ever sourced from a sink pool (a sink never loses funds in this flow) and every unit a sink gains
        // left the clone as a counted payout (sink growth is a subset of totalPaidOut). The exact forfeit
        // value is checked elsewhere. Under the frozen fixture voidAndAward is unreachable, so every delta
        // is 0.
        _assertSinkPoolsForfeitAware(paidOut);
    }

    /// @dev Forfeit-aware three-pool separation (extracted to keep invariant_FundConservation readable).
    ///      The sink pools (Treasury, OperatorBond) may only grow in this fund-safety flow (a forfeit
    ///      outflow from the clone), never shrink (no bidder principal is sourced from them), and their
    ///      combined growth over the setUp baseline can never exceed the clone's counted outflow (paidOut).
    ///      On the rail that is not the session payment currency no flow can occur, so that currency is
    ///      pinned to the baseline exactly.
    function _assertSinkPoolsForfeitAware(uint256 paidOut) internal view {
        uint256 treasuryEth = address(treasury).balance;
        uint256 operatorBondEth = address(operatorBond).balance;
        uint256 treasuryTok = token.balanceOf(address(treasury));
        uint256 operatorBondTok = token.balanceOf(address(operatorBond));

        // Sink pools never lose value in this flow (no bidder principal is sourced from a sink pool), on
        // both currencies.
        assertGe(treasuryEth, treasuryBaselineEth, "J-01: Treasury eth fell below baseline (sink pool leaked out)");
        assertGe(
            operatorBondEth,
            operatorBondBaselineEth,
            "J-01: OperatorBond eth fell below baseline (sink pool leaked out)"
        );
        assertGe(treasuryTok, treasuryBaselineToken, "J-01: Treasury token fell below baseline (sink pool leaked out)");
        assertGe(
            operatorBondTok,
            operatorBondBaselineToken,
            "J-01: OperatorBond token fell below baseline (sink pool leaked out)"
        );

        if (_nativeRail()) {
            // Payment currency is ETH: combined sink growth can never exceed the clone's counted outflow;
            // the non-payment currency (token) cannot move, so it is pinned to baseline exactly.
            uint256 sinkGrowthEth = (treasuryEth - treasuryBaselineEth) + (operatorBondEth - operatorBondBaselineEth);
            assertLe(sinkGrowthEth, paidOut, "J-01: sink-pool eth growth exceeds clone outflow (funds created)");
            assertEq(treasuryTok, treasuryBaselineToken, "J-01: Treasury token drift on the native rail");
            assertEq(operatorBondTok, operatorBondBaselineToken, "J-01: OperatorBond token drift on the native rail");
        } else {
            // Payment currency is the token: bound its sink growth by paidOut; pin ETH to baseline exactly.
            uint256 sinkGrowthTok =
                (treasuryTok - treasuryBaselineToken) + (operatorBondTok - operatorBondBaselineToken);
            assertLe(sinkGrowthTok, paidOut, "J-01: sink-pool token growth exceeds clone outflow (funds created)");
            assertEq(treasuryEth, treasuryBaselineEth, "J-01: Treasury eth drift on the ERC-20 rail");
            assertEq(operatorBondEth, operatorBondBaselineEth, "J-01: OperatorBond eth drift on the ERC-20 rail");
        }
    }

    /// J-02 (invariant_EscrowSingleExit): for every lot, lot.escrowAmount goes nonzero -> zero at most
    /// once and is never resurrected (nonzero again after a zeroing). Equivalently: the winner escrow is
    /// written once (hammer/promote) and zeroed by exactly one exit (_release / _refund / withdrawRefund
    /// step 2), then stays zero.
    function invariant_EscrowSingleExit() public view {
        uint256 nLots = handler.touchedLotsLength();
        for (uint256 i = 0; i < nLots; i++) {
            uint256 lotId = handler.touchedLotAt(i);
            assertLe(handler.escrowZeroings(lotId), 1, "J-02: escrow zeroed more than once (double-pay)");
            assertFalse(handler.escrowResurrected(lotId), "J-02: escrow re-set nonzero after a zeroing");

            // Set-once: escrowAmount is written exactly once, so it must never be overwritten from one
            // nonzero value to a different nonzero value without first being zeroed. The one legal exception
            // is the promote-time re-snapshot at voidAndAward (Hammered -> Voided), tracked and bounded
            // below; every other nonzero->nonzero overwrite trips this.
            assertFalse(
                handler.escrowMutatedWhileNonzero(lotId), "J-02: escrowAmount overwritten nonzero->nonzero (set-once)"
            );

            // Legal-promote bound: the single escrowAmount re-snapshot at voidAndAward (offender E1 ->
            // promoted E2 within one call) is compliant and must happen at most once per lot. A second
            // promote re-snapshot trips this, so set-once is enforced on the promote path too. Under the
            // frozen fixture no bid lands, so this stays 0.
            assertLe(
                handler.escrowResnapshots(lotId), 1, "J-02: escrowAmount re-snapshotted more than once at promote"
            );
        }
    }

    /// J-03 (invariant_DisputeBondPoolIsolation): the delivery dispute-bond pool (lot.disputeBond) is a
    /// closed, conserved pool disjoint from the bid escrow. Inflow is tracked from the openDispute pull
    /// intent (not inferred from disputeBond deltas, which can both miss and double-count); outflow is the
    /// observed disputeBond zero-transition. Total bond pulled in equals total paid out plus bond still
    /// held, and the pool never exceeds what was funded in (so escrow can never have leaked into the bond
    /// pool).
    function invariant_DisputeBondPoolIsolation() public view {
        uint256 bondStillHeld;
        uint256 nLots = handler.touchedLotsLength();

        for (uint256 i = 0; i < nLots; i++) {
            uint256 lotId = handler.touchedLotAt(i);
            bondStillHeld += auction.getLot(lotId).disputeBond;
        }

        // Closed-pool conservation: every bond unit pulled in is either still held or paid out; none is
        // created and none vanishes into (or is funded from) escrow.
        assertEq(
            handler.bondPulledIn(),
            handler.bondPaidOut() + bondStillHeld,
            "J-03: dispute-bond pool not conserved (bond in != out + held)"
        );

        // Disjointness: the bond still held can never exceed what was funded in (escrow never funds a
        // bond), and the bond pool sum can never exceed the whole clone balance.
        assertLe(bondStillHeld, handler.bondPulledIn(), "J-03: bond held exceeds bond funded (escrow leaked in)");
        assertLe(bondStillHeld, _railCloneBalance(), "J-03: bond held exceeds clone balance");

        // Recipient correctness: conservation is blind to a bond paid to the wrong party. On every
        // resolveDispute that paid the bond out, the handler asserted the rule-correct party (seller under
        // ReleaseToSeller, buyer under RefundToBuyer) gained at least the bond; this flag trips if it
        // reached someone else. Load-bearing once a Disputed lot can be resolved.
        for (uint256 i = 0; i < nLots; i++) {
            uint256 lotId = handler.touchedLotAt(i);
            assertFalse(
                handler.bondToWrongParty(lotId), "J-03: dispute bond credited the wrong party (not the winning party)"
            );

            // Exact recipient: the winner's gain must equal escrow-leg + bond exactly and the fee sink must
            // move by exactly the fee (ReleaseToSeller) / zero (RefundToBuyer). A bond split or redirected to
            // any third address satisfies the escrow-leg lower bound yet breaks this equality, so it bites
            // where the >= bond check and the loser-unchanged check pass.
            assertFalse(
                handler.bondNotExactToWinner(lotId),
                "J-03: dispute bond not paid in full to the winner (split / redirected to a third party)"
            );
        }
    }

    /// invariant_ClassBGateMonotonicity: lot.bidIntegrityOpen is incremented only by challengeAttestation
    /// (+1) and decremented only by resolveBidIntegrityDispute / timeoutBidIntegrityDispute (-1); it is
    /// never negative; the gate bidIntegrityDisputeOpen(lotId) is open iff the net open count is positive;
    /// and Class A (challengeOverCeiling) never flips it. The handler ghost-counts Class B opens / closes
    /// and Class A actions per lot.
    function invariant_ClassBGateMonotonicity() public view {
        uint256 nLots = handler.touchedLotsLength();
        for (uint256 i = 0; i < nLots; i++) {
            uint256 lotId = handler.touchedLotAt(i);
            uint256 opens = handler.classBOpens(lotId);
            uint256 closes = handler.classBCloses(lotId);

            // Never negative: a close (decrement) only ever fires against an existing open, so the
            // successful close count can never exceed the successful open count.
            assertLe(closes, opens, "item5: bidIntegrityOpen would go negative (more closes than opens)");

            // Gate open iff a Class B dispute is net-open.
            bool gate = auction.bidIntegrityDisputeOpen(lotId);
            assertEq(gate, opens > closes, "item5: gate open state != net Class B open count");

            // Class A (challengeOverCeiling) never flips the gate: a lot with Class A activity but no
            // net-open Class B dispute must read the gate closed.
            if (handler.classAActions(lotId) > 0 && opens == closes) {
                assertFalse(gate, "item5: Class A challengeOverCeiling wrongly opened the integrity gate");
            }

            // Gate blocks release: _release is reachable iff bidIntegrityOpen == 0, so the lot must never
            // advance to Settled while a Class B dispute is open (finalizeWinner and the release paths revert
            // BidIntegrityDisputeIsOpen while the gate is open). releasedWhileGateOpen is set by
            // _flagReleaseThroughGate, which snapshots the gate + phase before each release-driving call and
            // flags a real advance to Settled while the gate was open at the attempt, so the coupling holds
            // even if the same action (or a prior resolve/timeout) clears the gate before sync.
            assertFalse(
                handler.releasedWhileGateOpen(lotId),
                "item5: lot advanced to Settled while the Class B gate was open at the release attempt"
            );

            // Gate blocks release, fund level: the gate must keep escrow funds from leaving on a release
            // attempt. A buggy _release that pays the seller through an open gate but skips the terminal
            // Settled write slips the phase detector above yet leaks escrow (conservation stays neutral:
            // escrow out == paidOut). escrowPaidWhileGateOpen flags lot.escrowAmount going nonzero -> zero on
            // a release-driving call whose gate was open at the attempt.
            assertFalse(
                handler.escrowPaidWhileGateOpen(lotId),
                "item5: escrow paid out on a release attempt while the Class B gate was open"
            );
        }
    }

    /// invariant_NoStrandReachability: the terminals (Settled / Refunded / NoSale, and the DeliveryState
    /// Released / Refunded that map to them) have no outward escrow edge: once a lot is observed terminal,
    /// lot.escrowAmount must stay 0 for the rest of the run (a nonzero escrow afterward would be a stranded
    /// / re-opened escrow). The counterparty-independent exits (reclaimUndelivered, releaseAfterWindow, the
    /// bonded-dispute timeout) are driven every run, so reaching a terminal is exercised; this asserts
    /// terminals are absorbing for escrow.
    function invariant_NoStrandReachability() public view {
        uint256 nLots = handler.touchedLotsLength();
        for (uint256 i = 0; i < nLots; i++) {
            uint256 lotId = handler.touchedLotAt(i);
            assertFalse(
                handler.escrowAfterTerminal(lotId), "item6: escrow nonzero after a terminal phase (strand)"
            );
        }
    }

    /// invariant_NonTerminalHasIndependentExit (the liveness half): from every non-terminal delivery state
    /// a counterparty-independent exit must exist, so a vanished counterparty can never strand the escrow.
    /// Any lot that (a) rested non-terminal holding escrow in a state with an unconditional independent exit
    /// (AwaitingDelivery -> reclaimUndelivered for a vanished seller, Delivered -> releaseAfterWindow for a
    /// silent buyer), (b) had the clock warped past its frozen-anchor window, and (c) had that exit driven
    /// must have reached Settled or Refunded. A lot satisfying (a)+(b)+(c) but still non-terminal is a
    /// strand (the exit does not exist or is mis-anchored on endsAt). The Disputed escape (withdrawRefund
    /// step 3 for a vanished arbiter) is conditional on a prior voidSession and pinned by
    /// test_NoStrand_WithdrawRefundNotAnchoredOnEndsAt.
    ///
    /// Under the frozen fixture placeBid never lands, so no lot enters a non-terminal delivery state and the
    /// antecedent is never satisfied; the property holds soundly and becomes load-bearing once bids land.
    /// The fixture-independent anchoring pin (the exit is gated on the frozen anchor, never on endsAt) lives
    /// in the test_NoStrand_* units below.
    function invariant_NonTerminalHasIndependentExit() public view {
        uint256 nLots = handler.touchedLotsLength();
        for (uint256 i = 0; i < nLots; i++) {
            uint256 lotId = handler.touchedLotAt(i);
            // Antecedent: a matching unconditional independent exit was attempted under its exact
            // precondition (set in reclaim / releaseWindow: correct DeliveryState, past the frozen window,
            // Class B gate closed for release, session not voided). That arming guarantees the exit must
            // settle the lot, so independentExitAttempted alone is the sound antecedent: a lot that did not
            // reach a terminal has no exit / is mis-anchored. A check-time gate guard is deliberately not
            // used: it could mask a real strand (a Class B dispute opened on the stuck lot would suppress
            // the assertion).
            if (handler.independentExitAttempted(lotId)) {
                assertTrue(
                    handler.reachedTerminalAfterExit(lotId),
                    "item6: a frozen-window counterparty-independent exit failed to reach terminal (strand)"
                );
            }
        }
    }

    /// invariant_NonceReplayMonotonicity: _useCheckedNonce enforces a strictly sequential bidIndex per
    /// (principal, nonceKey), and _quoteNonceUsed[keyId][nonce] is set at most once per (operatorKeyId,
    /// quote.nonce); neither can be replayed. The handler re-drives the same (principal, nonceKey, bidIndex)
    /// and (operatorKeyId, quote.nonce) via placeBid + replayBid, counting every success; a replay that
    /// succeeded a second time would push a counter past one and trip this.
    ///
    /// Fixture caveat: HammerBase's pinned operator key fixture (keccak256("OPERATOR_QX_FIXTURE")/
    /// ("OPERATOR_QY_FIXTURE")) is not a valid P-256 keypair with a known scalar, so the handler cannot
    /// forge a passing P256 attestation and placeBid never succeeds even in green; the success counters stay
    /// 0 and the <= 1 bound holds soundly. The per-unit replay reverts (InvalidAccountNonce, QuoteNonceUsed)
    /// are covered elsewhere; this is the stateful backstop that becomes load-bearing once a valid operator
    /// keypair lets placeBid land.
    function invariant_NonceReplayMonotonicity() public view {
        // Sweep the (principal, nonceKey, bidIndex) and (operatorKeyId, quote.nonce) keys the handler can
        // produce: principals x lots x bidIndex in [0,4], with the single operatorKeyId == 0 and
        // quote.nonce == bytes32(bidIndex). Any double-success is a replay.
        uint256 nPrincipals = handler.principalsLength();
        for (uint256 li = 0; li < 3; li++) {
            for (uint256 pi = 0; pi < nPrincipals; pi++) {
                address who = handler.principalAt(pi);
                uint192 nonceKey = uint192(uint256(keccak256(abi.encode(bytes32(0), li, who))));
                for (uint64 bi = 0; bi <= 4; bi++) {
                    bytes32 k = keccak256(abi.encode(who, nonceKey, bi));
                    assertLe(
                        handler.bidIndexSuccessCount(k), 1, "item7: same (principal,nonceKey,bidIndex) succeeded twice"
                    );
                    bytes32 qk = keccak256(abi.encode(bytes32(0), bytes32(uint256(bi))));
                    assertLe(
                        handler.quoteNonceSuccessCount(qk), 1, "item7: same (operatorKeyId,quote.nonce) reused"
                    );
                }
            }
        }
    }

    /// afterInvariant liveness gate: the conservation / single-exit / pool-isolation predicates all hold
    /// vacuously when no fund-moving call ever succeeds (every bucket stays 0), so this asserts the handler
    /// moved funds at least once. depositSuccesses is the primary red signal: it is green-achievable
    /// (depositCeiling needs no bid), so a vacuous run fails here.
    function afterInvariant() public {
        // Primary red signal, unconditional and green-achievable: at least one pull-side fund movement fired.
        assertGt(handler.depositSuccesses(), 0, "liveness: no deposit ever succeeded (invariants held vacuously)");

        // Strengthened per-subject liveness: depositSuccesses proves only one pull-side action fired, not
        // that the escrow / bond / Class-B-gate machinery each invariant is about ever advanced. Each assert
        // below names the sub-property whose subject transition must have fired.
        //
        // Gated on bidSuccesses > 0 because escrow, dispute bonds, and the Class B gate are all downstream
        // of an accepted bid, which the frozen fixture cannot produce; an unconditional gate would
        // false-red the domain forever. Gating keeps them dormant under the fixture and bites the moment
        // bids land (same posture as invariant_NonceReplayMonotonicity).
        if (handler.bidSuccesses() > 0) {
            uint256 nLots = handler.touchedLotsLength();
            uint256 escrowZeroingsSum;
            uint256 classBOpensSum;
            uint256 classBClosesSum;
            for (uint256 i = 0; i < nLots; i++) {
                uint256 lotId = handler.touchedLotAt(i);
                escrowZeroingsSum += handler.escrowZeroings(lotId);
                classBOpensSum += handler.classBOpens(lotId);
                classBClosesSum += handler.classBCloses(lotId);
            }
            // J-02 saw a real escrow exit (an escrowAmount nonzero -> zero transition actually happened).
            assertGt(escrowZeroingsSum, 0, "liveness: J-02 vacuous (no escrow exit ever fired)");
            // J-03 moved a bond (a bond was pulled in or paid out at least once).
            assertGt(
                handler.bondPulledIn() + handler.bondPaidOut(), 0, "liveness: J-03 vacuous (no dispute bond ever moved)"
            );
            // Item 5 opened AND closed the Class B gate at least once (the gate transition under test).
            assertGt(classBOpensSum, 0, "liveness: item5 vacuous (Class B gate never opened)");
            assertGt(classBClosesSum, 0, "liveness: item5 vacuous (Class B gate never closed)");
        }
    }

    // J-02 companions: every escrow-paying entrypoint fails closed from an illegal pre-state. On a fresh
    // lot (phase None, deliveryState None, not session-voided) each escrow-paying call reverts on its first
    // guard with a specific selector, never reaching a _pay, so escrow cannot leave from any state but the
    // one legal terminal edge. The NoEscrow double-pay after a real exit (escrowAmount already zeroed) needs
    // the full green machine and is covered by invariant_EscrowSingleExit.

    /// confirmReceipt is onlyBuyer (msg.sender == lot.highBidder). On a fresh lot highBidder is
    /// address(0), so a non-buyer caller reverts Unauthorized before the escrow leg.
    function test_EscrowSingleExit_ConfirmReceiptFailsClosed() public {
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.confirmReceipt(0, keccak256("photo"), "cid");
    }

    /// releaseAfterWindow is permissionless but requires deliveryState == Delivered; a fresh lot
    /// (deliveryState None) reverts WrongDeliveryState before the escrow leg.
    function test_EscrowSingleExit_ReleaseAfterWindowFailsClosed() public {
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.releaseAfterWindow(0);
    }

    /// reclaimUndelivered is onlyBuyer; a non-buyer caller on a fresh lot (highBidder address(0))
    /// reverts Unauthorized before the escrow leg.
    function test_EscrowSingleExit_ReclaimUndeliveredFailsClosed() public {
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.reclaimUndelivered(0);
    }

    /// resolveDispute is onlyArbiter then requires deliveryState == Disputed; the arbiter caller on a
    /// fresh lot (deliveryState None) reverts WrongDeliveryState before either escrow leg. Both legs
    /// (ReleaseToSeller / RefundToBuyer) zero the same escrow slot, so neither can fire here.
    function test_EscrowSingleExit_ResolveDisputeFailsClosed() public {
        vm.prank(arbiter);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.resolveDispute(0, Resolution.ReleaseToSeller, keccak256("photo"));
    }

    /// withdrawRefund guards `!_sessionVoided && !_isTerminalRefundable(phase)` and reverts
    /// SessionIsVoided first. A fresh lot is neither session-voided nor terminal-refundable, so the
    /// winner-escrow exit (step 2) is unreachable here.
    function test_EscrowSingleExit_WithdrawRefundFailsClosed() public {
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.SessionIsVoided.selector);
        auction.withdrawRefund(0);
    }

    // J-03 companion: dispute-bond inflow fails closed. The pool's sole inflow (the openDispute bond pull)
    // fails closed from an illegal pre-state: no bond can be pulled into lot.disputeBond from a lot not
    // legitimately disputable by this caller, so the closed pool is never seeded from a state the resolver
    // cannot later pay out. These pin the openDispute pre-pull guards (caller-identity first, then state)
    // with specific selectors.

    /// openDispute is restricted to the lot's buyer (highBidder) or seller, else Unauthorized, and that
    /// caller-identity check precedes the state check and the bond _pull. On a fresh lot highBidder and
    /// seller are both address(0), so a third-party opener (bidder1) is neither party and reverts
    /// Unauthorized before _pull can move any value. payable with the exact bond so the revert is the
    /// identity guard, not a value mismatch.
    function test_DisputeBondInflowFailsClosed_NonPartyOpener() public {
        vm.deal(bidder1, bidder1.balance + DISPUTE_BOND_AMT);
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.openDispute{value: DISPUTE_BOND_AMT}(0, keccak256("claim"));
    }

    /// openDispute's seller path cannot be impersonated either: a caller that is not the recorded seller is
    /// rejected by the same Unauthorized guard. Pranking an unregistered stranger (neither the zero
    /// highBidder nor the zero seller) on a fresh lot reverts Unauthorized before the bond pull, so no
    /// degenerate "msg.sender == address(0)" opener exists. A distinct adversarial caller from bidder1
    /// above, pinning the inflow gate against any non-party.
    function test_DisputeBondInflowFailsClosed_StrangerOpener() public {
        address stranger = makeAddr("disputeStranger");
        vm.deal(stranger, stranger.balance + DISPUTE_BOND_AMT);
        vm.prank(stranger);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.openDispute{value: DISPUTE_BOND_AMT}(0, keccak256("claim"));
    }

    /// J-02 companion: delivery-pipeline entry fails closed. markDelivered is the entry to the release
    /// pipeline (the only edge from AwaitingDelivery to Delivered, the precondition for confirmReceipt /
    /// releaseAfterWindow / openDispute-on-Delivered). It is onlySeller (msg.sender == lot.seller). On a
    /// fresh lot seller is address(0), so a non-seller caller reverts Unauthorized and cannot drive the
    /// delivery state machine that gates _release.
    function test_EscrowSingleExit_MarkDeliveredFailsClosed() public {
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.markDelivered(0, keccak256("proof"), "cid");
    }

    // No-strand liveness anchoring pins: the counterparty-independent exits are gated on frozen delivery
    // anchors, never on the soft-close-slid endsAt.

    /// No-strand anchoring. The counterparty-independent exits are gated on the frozen delivery anchors
    /// (awaitingAt + sellerDeliverSec, deliveredAt + disputeWindowSec), never on endsAt (which the soft
    /// close slides). Warps far past endsAt and past where any endsAt-anchored window would have elapsed,
    /// then proves the exit on a fresh lot still fails closed on its state guard, so time-past-endsAt alone
    /// never opens it.
    ///
    /// releaseAfterWindow is permissionless (no access gate masks the state guard): on a fresh lot
    /// (deliveryState None) it reverts WrongDeliveryState before the window check, proving the gate is
    /// anchored on deliveredAt, not endsAt.
    function test_NoStrand_ReleaseAfterWindowNotAnchoredOnEndsAt() public {
        // Warp past endsAt (lots open with endsAt == setUp + 1 day) and past endsAt + the longest delivery
        // window (sellerDeliverSec 7d + disputeWindowSec 3d), so an endsAt-anchored bug would consider the
        // window elapsed; still under sessionEnd (setUp + 30 days).
        vm.warp(block.timestamp + 12 days);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.releaseAfterWindow(0);
    }

    /// No-strand anchoring (vanished-seller exit). reclaimUndelivered is onlyBuyer, so the access gate fires
    /// first: a non-buyer caller reverts Unauthorized even warped far past endsAt, proving the no-strand
    /// reclaim is gated by identity + the frozen awaitingAt window, not opened by the clock passing endsAt.
    function test_NoStrand_ReclaimUndeliveredNotAnchoredOnEndsAt() public {
        vm.warp(block.timestamp + 12 days);
        vm.prank(bidder1); // not the buyer (highBidder is address(0) on a fresh lot)
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.reclaimUndelivered(0);
    }

    /// No-strand anchoring (Disputed / vanished-arbiter exit). The Disputed-lot strand-escape is
    /// withdrawRefund step 3 (return the bond to the opener once resolveDispute can no longer fire under a
    /// session void). On a fresh, non-voided lot, withdrawRefund reverts SessionIsVoided first, independent
    /// of how far past endsAt the clock is warped: the universal pull exit is gated by the void flag +
    /// terminal-refundable state, never by endsAt. (The fresh-lot SessionIsVoided guard is also pinned by
    /// test_EscrowSingleExit_WithdrawRefundFailsClosed; here the warp proves endsAt-independence.)
    function test_NoStrand_WithdrawRefundNotAnchoredOnEndsAt() public {
        vm.warp(block.timestamp + 12 days);
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.SessionIsVoided.selector);
        auction.withdrawRefund(0);
    }

    /// No-strand anchoring (Class B integrity timeout). timeoutBidIntegrityDispute is the permissionless
    /// auto-resolve that prevents an unanswered Class B challenge from freezing the seller's _release
    /// forever. It is anchored on the frozen _integrityDispute.openedAt + _integrityTimeoutSec, never on
    /// endsAt. The sibling no-strand pins cover the delivery exits; this one covers the integrity timeout,
    /// guarding against a regression that anchors it on the soft-close-slid endsAt.
    ///
    /// Warps block.timestamp far past endsAt and past where any endsAt-anchored window would have elapsed,
    /// then proves the timeout on a fresh lot still fails closed on its open/Class-B guard. On a fresh lot
    /// the dispute is not open and openedAt == 0, so the window-open gate (which reverts only while
    /// block.timestamp < openedAt + _integrityTimeoutSec) passes after the warp, leaving the not-open /
    /// not-Class-B guard (WrongDeliveryState) as the first revert. That proves the timeout exit is gated on
    /// the frozen openedAt state, not auto-opened by the auction clock passing endsAt: an endsAt-anchored
    /// timeout would key its window on the slid endsAt rather than the frozen openedAt.
    function test_NoStrand_IntegrityTimeoutNotAnchoredOnEndsAt() public {
        // 12 days clears endsAt (setUp + 1 day), endsAt + the longest delivery window (10 days), and
        // openedAt(0) + _integrityTimeoutSec (2 days), so the window-open gate is satisfied and an
        // endsAt-anchored bug would treat the timeout window as elapsed; still under sessionEnd (30 days).
        vm.warp(block.timestamp + 12 days);
        vm.expectRevert(ISessionAuction.WrongDeliveryState.selector);
        auction.timeoutBidIntegrityDispute(0, 0);
    }

    // Reentrancy adversary on the fund-exit paths.

    /// Reentrancy fund-safety. The defense is the gas-capped native _pay (call{gas:50_000} with a
    /// pending-withdrawal fallback): a reentrant recipient's nested call runs inside the 50k-gas push frame,
    /// so even though the nested nonReentrant call reverts ReentrancyGuardReentrantCall, that revert is
    /// caught by _pay and the funds are credited to _pendingWithdrawals rather than double-paid. The outer
    /// call therefore does not surface ReentrancyGuardReentrantCall (asserting it would false-fail), so the
    /// load-bearing guarantee is conservation: a reentrant recipient can never extract more than it was
    /// owed. The primary catch is the stateful run, where FundReentrantRecipient is a registered handler
    /// principal and any reentrant double-pay breaks conservation and single-exit automatically. This direct
    /// unit pins the per-call property: the attacker, armed to re-enter, cannot grow its total claimable by
    /// more than it deposited.
    function test_ReentrantWithdrawCannotDoublePay() public {
        // Recipient-callback reentrancy is a native-rail concern: the ERC-20 push uses
        // SafeERC20.trySafeTransfer, which hands no execution to a standard recipient, so there is no
        // callback to re-enter from. On the ERC-20 concrete this property is vacuous; assert it only on the
        // native rail where the gas-capped call{gas:50_000} push is the reentry vector.
        if (!_nativeRail()) return;

        uint256 depositAmt = 5 ether;

        // Arm the attacker to re-enter withdrawDeposit on every native push it receives.
        attacker.arm(ISessionAuction(address(auction)), 0, depositAmt);

        // Attacker funds a deposit, pranked as the attacker so it is keyed to its principal.
        vm.deal(address(attacker), address(attacker).balance + depositAmt);
        vm.prank(address(attacker));
        try auction.depositCeiling{value: depositAmt}(0, depositAmt) {} catch {}

        uint256 claimableBefore = address(attacker).balance + auction.pendingWithdrawal(address(attacker));

        // Attacker withdraws, whose native push re-enters withdrawDeposit. The gas-capped _pay catches the
        // reentrant revert and credits pending; no double-pay can occur.
        vm.prank(address(attacker));
        try auction.withdrawDeposit(0, depositAmt) {} catch {}

        uint256 claimableAfter = address(attacker).balance + auction.pendingWithdrawal(address(attacker));

        // The attacker can never end up better off than the single deposit it funded. A reentrant
        // double-pay would push the gain above depositAmt and trip this. Disarm so later test teardown is
        // inert.
        attacker.disarm();
        assertLe(
            claimableAfter - claimableBefore,
            depositAmt,
            "reentrancy: attacker extracted more than its deposit (double-pay via push re-entry)"
        );
    }

    /// Reentrancy fund-safety, release-exit variant. Probes a seller-paying exit other than withdrawDeposit:
    /// the registered-principal attacker is armed to re-enter releaseAfterWindow during the native push of
    /// its own withdrawDeposit. The shared ReentrancyGuardTransient makes the nested releaseAfterWindow
    /// revert ReentrancyGuardReentrantCall (caught by the gas-capped _pay -> pending credit); if
    /// releaseAfterWindow were authored without nonReentrant, the nested call would proceed and could push
    /// escrow mid-withdraw, growing the attacker's claimable past its deposit and tripping the same
    /// no-double-pay conservation bound. The bound is load-bearing per exit, not just for withdrawDeposit.
    function test_ReentrantReleaseAfterWindowCannotDoublePay() public {
        if (!_nativeRail()) return;

        uint256 depositAmt = 5 ether;

        // Arm to re-enter releaseAfterWindow(lot 0) on every native push: probe a different seller-paying
        // exit than withdrawDeposit.
        attacker.armMode(
            ISessionAuction(address(auction)), FundReentrantRecipient.ReenterMode.ReleaseAfterWindow, 0, depositAmt
        );

        vm.deal(address(attacker), address(attacker).balance + depositAmt);
        vm.prank(address(attacker));
        try auction.depositCeiling{value: depositAmt}(0, depositAmt) {} catch {}

        uint256 claimableBefore = address(attacker).balance + auction.pendingWithdrawal(address(attacker));

        // The withdraw push re-enters releaseAfterWindow; a missing-nonReentrant on that exit would let it
        // double-fire here.
        vm.prank(address(attacker));
        try auction.withdrawDeposit(0, depositAmt) {} catch {}

        uint256 claimableAfter = address(attacker).balance + auction.pendingWithdrawal(address(attacker));

        attacker.disarm();
        assertLe(
            claimableAfter - claimableBefore,
            depositAmt,
            "reentrancy: re-entry into releaseAfterWindow extracted more than the deposit (missing nonReentrant on a seller-paying exit)"
        );
    }

    /// Reentrancy fund-safety, claim-pending-exit variant (second exit probe). claimPending is the
    /// failed-push drain; if it were authored without nonReentrant, a recipient could re-enter it during
    /// another exit's push and drain its pending credit twice. The attacker is armed to re-enter claimPending
    /// during the native push of its own withdrawDeposit. The shared transient guard makes the nested
    /// claimPending revert ReentrancyGuardReentrantCall (caught -> pending credit), so the attacker never
    /// extracts more than the single deposit it funded. Pins that claimPending specifically carries the
    /// guard.
    function test_ReentrantClaimPendingCannotDoublePay() public {
        if (!_nativeRail()) return;

        uint256 depositAmt = 5 ether;

        attacker.armMode(
            ISessionAuction(address(auction)), FundReentrantRecipient.ReenterMode.ClaimPending, 0, depositAmt
        );

        vm.deal(address(attacker), address(attacker).balance + depositAmt);
        vm.prank(address(attacker));
        try auction.depositCeiling{value: depositAmt}(0, depositAmt) {} catch {}

        uint256 claimableBefore = address(attacker).balance + auction.pendingWithdrawal(address(attacker));

        // The withdraw push re-enters claimPending; a missing-nonReentrant there would let the pending
        // credit drain re-fire mid-withdraw.
        vm.prank(address(attacker));
        try auction.withdrawDeposit(0, depositAmt) {} catch {}

        uint256 claimableAfter = address(attacker).balance + auction.pendingWithdrawal(address(attacker));

        attacker.disarm();
        assertLe(
            claimableAfter - claimableBefore,
            depositAmt,
            "reentrancy: re-entry into claimPending extracted more than the deposit (missing nonReentrant on the pending drain)"
        );
    }

    /// J-04 (test_StorageLayoutBaseline): the canonical packed Lot layout and the bid-path / integrity /
    /// operator record types exist at their documented widths. The authoritative CI gate is
    /// `forge inspect SessionAuction storageLayout` against a committed baseline; this test pins the same
    /// surface structurally so a field widened/narrowed/reordered changes the decoded struct and trips an
    /// assert. The split test_J04_* functions below each drive a real entrypoint touching a named storage
    /// region.
    function test_StorageLayoutBaseline() public view {
        // Hot slot 0 + slot 1 + the cold slots, decoded to the canonical default widths.
        Lot memory lot = auction.getLot(0);
        assertEq(uint256(lot.highBid), 0, "J-04: highBid slot");
        assertEq(uint256(lot.endsAt), 0, "J-04: endsAt slot");
        assertEq(uint256(lot.paddleId), 0, "J-04: paddleId slot");
        assertEq(uint256(lot.sealedExtensions), 0, "J-04: sealedExtensions slot");
        assertEq(uint256(lot.phase), uint256(uint8(LotPhase.None)), "J-04: phase slot (hot slot 0)");
        assertEq(
            uint256(lot.deliveryState), uint256(uint8(DeliveryState.None)), "J-04: deliveryState slot (hot slot 0)"
        );
        assertEq(lot.highBidder, address(0), "J-04: highBidder slot 1");
        assertEq(uint256(lot.hammeredAt), 0, "J-04: hammeredAt slot 1");
        assertEq(uint256(lot.voidedAt), 0, "J-04: voidedAt slot 1");
        assertEq(lot.revealed, false, "J-04: revealed slot 1 flag");
        assertEq(uint256(lot.bidIntegrityOpen), 0, "J-04: bidIntegrityOpen slot 1 counter");
        assertEq(lot.seller, address(0), "J-04: seller slot 2");
        assertEq(uint256(lot.awaitingAt), 0, "J-04: awaitingAt slot 2");
        assertEq(uint256(lot.deliveredAt), 0, "J-04: deliveredAt slot 2");
        assertEq(uint256(lot.reservePrice), 0, "J-04: reservePrice slot 3");
        assertEq(uint256(lot.escrowAmount), 0, "J-04: escrowAmount slot 3");
        // winnerSeq's fresh-slot-4 placement is pinned at its zero state here; a nonzero round-trip requires
        // a hammered winner (a successful placeBid), which the frozen non-P256 fixture cannot produce through
        // this harness, so the nonzero exercise is deferred to the forge-inspect storage baseline and the
        // green lifecycle tests.
        assertEq(uint256(lot.winnerSeq), 0, "J-04: winnerSeq fresh slot 4 (CORR-1)");
        assertEq(lot.bidBookRoot, bytes32(0), "J-04: bidBookRoot slot 5");
        assertEq(lot.deliveryProofHash, bytes32(0), "J-04: deliveryProofHash slot 6");
        assertEq(lot.disputeOpener, address(0), "J-04: disputeOpener slot 7");
        assertEq(uint256(lot.disputeBond), 0, "J-04: disputeBond slot 7");
        assertEq(lot.disputeRef, bytes32(0), "J-04: disputeRef slot 8");

        // The Deposit and IntegrityDispute records (the _deposit and _integrityDispute storage types)
        // decode at their documented widths. Constructed in-memory to pin the struct shape the storage
        // mappings use; a width drift would fail to compile or mis-decode.
        Deposit memory d = Deposit({free: type(uint128).max, committed: type(uint128).max});
        assertEq(uint256(d.free), uint256(type(uint128).max), "J-04: Deposit.free width");
        assertEq(uint256(d.committed), uint256(type(uint128).max), "J-04: Deposit.committed width");

        IntegrityDispute memory id = IntegrityDispute({
            challenger: address(this),
            bond: type(uint96).max,
            openedAt: type(uint40).max,
            open: true,
            class: 1
        });
        assertEq(uint256(id.bond), uint256(type(uint96).max), "J-04: IntegrityDispute.bond width (u96)");
        assertEq(uint256(id.openedAt), uint256(type(uint40).max), "J-04: IntegrityDispute.openedAt width (u40)");
        assertEq(uint256(id.class), 1, "J-04: IntegrityDispute.class width (u8, Class B == 1)");

        // The integrity gate view pins to the canonical zero state for a fresh lot (slot 1 counter 0).
        assertEq(auction.bidIntegrityDisputeOpen(0), false, "J-04: bidIntegrityOpen counter starts at 0");
    }

    // Split J-04 region drivers: each drives a real entrypoint whose write touches a named storage region,
    // asserting a specific selector that is independent of pre-state.

    /// _operatorKeys / _operatorActive region: registerOperatorKey is onlyHammer. A non-hammer caller
    /// reverts Unauthorized, exercising the operator-roster gate.
    function test_J04_OperatorRosterGate() public {
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.registerOperatorKey(keccak256("qx_J04"), keccak256("qy_J04"));
    }

    /// _bidOf / winnerSeq / hot slot 0 region: placeBid with an empty signature for an EOA principal
    /// (code.length == 0) routes to ECDSA recovery, which fails on the empty sig, so _authorizeBid
    /// reverts BadSignature before any state write.
    function test_J04_BidPathStorageWrite() public {
        // Lot 2 is the still-Open fuzzer lot (lot 1 is seeded to a terminal in setUp, so a placeBid there
        // would revert NotOpen before the signature check). An empty signature must fail closed.
        Ceiling memory c = Ceiling({
            principal: bidder1,
            sessionId: SESSION_ID,
            lotId: 2,
            ceilingCommit: keccak256(abi.encode(uint128(1 ether), keccak256("salt"))),
            strategy: 0,
            deadline: uint64(block.timestamp + 1 days),
            maxBids: 64,
            nonceKey: uint192(uint256(keccak256(abi.encode(SESSION_ID, uint256(2), bidder1))))
        });
        AttestationQuote memory q = AttestationQuote({
            mrEnclave: MR_ENCLAVE,
            vendorRoot: VENDOR_ROOT,
            observedPrevTop: bytes32(0),
            nonce: keccak256("qn"),
            r: bytes32(0),
            s: bytes32(0)
        });
        vm.expectRevert(ISessionAuction.BadSignature.selector);
        auction.placeBid(c, 2, bidder1, 0, uint128(1 ether), "", bytes32(0), q);
    }

    /// lot.revealed / winnerSeq region: reveal binds the winning seq. lot.winnerSeq is 0 (no bid hammered),
    /// so revealing seq == 1 trips the seq binding and reverts WrongSeq.
    function test_J04_RevealSeqBinding() public {
        vm.prank(bidder1);
        vm.expectRevert(ISessionAuction.WrongSeq.selector);
        auction.reveal(0, 1, uint128(1 ether), keccak256("salt"));
    }

    /// lot.bidIntegrityOpen / _integrityDispute region: resolveBidIntegrityDispute is the onlyArbiter
    /// resolver that writes _integrityDispute and decrements lot.bidIntegrityOpen. A non-arbiter caller
    /// reverts Unauthorized before any state read, exercising that region's access gate.
    function test_J04_IntegrityResolverGate() public {
        vm.expectRevert(ISessionAuction.Unauthorized.selector);
        auction.resolveBidIntegrityDispute(0, 0, true, 0);
    }
}

// FundInvariantsTest: the native rail concrete (paymentToken == address(0)). Runs every fund-safety
// property against address(auction).balance.
contract FundInvariantsTest is FundInvariantsBase {
    function _nativeRail() internal pure override returns (bool) {
        return true;
    }

    function _paymentToken() internal pure override returns (address) {
        return address(0);
    }
}

// FundInvariantsErc20Test: the ERC-20 rail concrete (paymentToken == the 6-decimal MockERC20). Runs the
// identical properties against token.balanceOf(address(auction)), satisfying the both-rails conservation
// mandate. The handler mints + approves the pulled token amount inside each pull-side action, so the
// token-balance conservation identity runs against real token flows and Treasury / OperatorBond token
// drift is checked against a baseline that can actually move.
contract FundInvariantsErc20Test is FundInvariantsBase {
    function _nativeRail() internal pure override returns (bool) {
        return false;
    }

    function _paymentToken() internal view override returns (address) {
        return address(token);
    }
}

// FundReentrantRecipient: a malicious payee whose receive()/fallback re-enters the auction during any
// native push it receives (the ERC777-style fund-drain a fund-safety suite must exercise). Registered as
// a handler principal on both rails so escrow/bond pushes can target it. Because the native push is
// gas-capped (call{gas:50_000}) with a pending-withdrawal fallback, the reentrant nonReentrant call
// reverts ReentrancyGuardReentrantCall inside the capped frame and is caught by _pay (the funds go to
// pending, never double-paid), so the conservation invariants are what catch a double-pay, not an outer
// revert. Uniquely named so it cannot collide with any other test file's helper symbols.
contract FundReentrantRecipient {
    // Re-entry target exit. Parameterized so a unit test can arm the same registered-principal attacker to
    // re-enter any exit during a native push, exercising the shared ReentrancyGuardTransient per exit
    // rather than only via withdrawDeposit.
    enum ReenterMode {
        WithdrawDeposit, // 0  withdrawDeposit(lotId, amount)   (the original, default)
        ReleaseAfterWindow, // 1  releaseAfterWindow(lotId)        (permissionless seller-paying exit)
        ClaimPending, // 2  claimPending()                    (failed-push drain)
        ReclaimUndelivered, // 3  reclaimUndelivered(lotId)         (buyer no-strand refund)
        WithdrawRefund // 4  withdrawRefund(lotId)             (universal pull exit, void path)
    }

    ISessionAuction internal target;
    ReenterMode internal mode;
    uint256 internal reenterLotId;
    uint256 internal reenterAmount;
    bool internal armed;
    bool internal entered; // re-entry latch: prevents nested recursion within a single outer push

    constructor(ISessionAuction _target) {
        target = _target;
    }

    /// @notice Arm the recipient to re-enter withdrawDeposit(lotId, amount) on the next push (the default
    ///         mode), optionally repointing the target clone.
    function arm(ISessionAuction _target, uint256 lotId, uint256 amount) external {
        target = _target;
        mode = ReenterMode.WithdrawDeposit;
        reenterLotId = lotId;
        reenterAmount = amount;
        armed = true;
        entered = false;
    }

    /// @notice Arm the recipient to re-enter a specific exit (`m`) on the next push, so the same attacker
    ///         can probe a missing-nonReentrant on releaseAfterWindow / claimPending / reclaimUndelivered /
    ///         withdrawRefund, not only withdrawDeposit.
    function armMode(ISessionAuction _target, ReenterMode m, uint256 lotId, uint256 amount) external {
        target = _target;
        mode = m;
        reenterLotId = lotId;
        reenterAmount = amount;
        armed = true;
        entered = false;
    }

    /// @notice Stop re-entering (used after a unit test so later teardown pushes are inert).
    function disarm() external {
        armed = false;
    }

    /// @dev On receiving a native push, re-enter the armed exit. The `entered` flag is set before the
    ///      nested call and cleared after, so it re-arms for each distinct outer push but cannot recurse
    ///      infinitely (a nested push during the re-entrant call sees `entered == true` and skips). Every
    ///      targeted exit is a nonReentrant entrypoint, so it reverts ReentrancyGuardReentrantCall; that
    ///      revert bubbles into the gas-capped _pay frame of the outer call and is swallowed (pending
    ///      credit), so no double-pay occurs. A missing nonReentrant on the armed exit would instead let the
    ///      nested call proceed and double-fire, which the no-double-pay conservation bound then catches.
    ///      The try/catch keeps this frame from propagating regardless.
    function _reenter() private {
        if (armed && !entered) {
            entered = true;
            ReenterMode m = mode;
            if (m == ReenterMode.WithdrawDeposit) {
                try target.withdrawDeposit(reenterLotId, reenterAmount) {} catch {}
            } else if (m == ReenterMode.ReleaseAfterWindow) {
                try target.releaseAfterWindow(reenterLotId) {} catch {}
            } else if (m == ReenterMode.ClaimPending) {
                try target.claimPending() {} catch {}
            } else if (m == ReenterMode.ReclaimUndelivered) {
                try target.reclaimUndelivered(reenterLotId) {} catch {}
            } else {
                try target.withdrawRefund(reenterLotId) {} catch {}
            }
            entered = false;
        }
    }

    receive() external payable {
        _reenter();
    }

    fallback() external payable {
        _reenter();
    }
}
