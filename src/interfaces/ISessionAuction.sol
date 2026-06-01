// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {
    Ceiling,
    AttestationQuote,
    NextCleanCandidate,
    InitConfig,
    Lot,
    Resolution
} from "../types/HammerTypes.sol";

/// @title ISessionAuction
/// @notice External surface of the per-session auction clone: lifecycle, funding,
///         bidding, hammer/finalize, anti-collusion, delivery settlement, and
///         bid-integrity disputes.
interface ISessionAuction {
    // Events. Each is limited to 3 indexed topics.

    // funding / escrow
    event CeilingDeposited(uint256 indexed lotId, address indexed principal, uint256 amount, uint256 newFree);
    event DepositWithdrawn(uint256 indexed lotId, address indexed principal, uint256 amount);
    event BidPlaced(uint256 indexed lotId, address indexed principal, uint128 amount, uint64 seq);
    event TopBidChanged(uint256 indexed lotId, address indexed principal, uint128 amount);
    event BidEscrowCommitted(uint256 indexed lotId, address indexed principal, uint128 committed, address previousTop, uint128 previousReleased);
    event AuctionExtended(uint256 indexed lotId, uint64 newEndsAt);
    event WithdrawalCredited(address indexed account, uint256 amount);
    event WithdrawalClaimed(address indexed account, uint256 amount);

    // lifecycle
    event Hammered(uint256 indexed lotId, address indexed winner, uint128 amount);
    event NoSale(uint256 indexed lotId);                       // lot closed with no winning bid
    event BidBookCommitted(uint256 indexed lotId, bytes32 root);
    event WinnerFinalized(uint256 indexed lotId, address indexed winner, uint128 amount);

    // anti-collusion
    event LotVoided(uint256 indexed lotId, address indexed offender, address indexed promotedWinner, uint128 promotedAmount);
    event LotNonLivenessSlashed(uint256 indexed lotId); // operator pool slashed for a funded lot that drew no bid
    event SessionVoided(bytes32 indexed sessionId, string reason);

    // delivery settlement
    event Delivered(uint256 indexed lotId, bytes32 proofHash, string cid);
    event Confirmed(uint256 indexed lotId, bytes32 photoHash, string cid);
    event Released(uint256 indexed lotId, address indexed seller, uint256 proceeds, uint256 fee);
    event Refunded(uint256 indexed lotId, address indexed buyer, uint256 amount);
    event DeliveryAutoReleased(uint256 indexed lotId, address indexed seller);
    event ReclaimedUndelivered(uint256 indexed lotId, address indexed buyer, uint128 amount);
    event DisputeOpened(uint256 indexed lotId, address indexed opener, uint256 bond, bytes32 claimRef);
    event DisputeResolved(uint256 indexed lotId, Resolution resolution, address indexed bondRecipient);

    // identity / integrity
    event EnvelopeCancelled(address indexed principal, uint192 indexed nonceKey);
    event BidIntegrityDisputeOpened(uint256 indexed lotId, uint64 indexed seq, address indexed by, uint8 class, uint256 bond); // bond is 0 for the over-ceiling class
    event BidIntegrityClaimUpheld(uint256 indexed lotId, uint64 indexed seq, address indexed victim, uint128 provenHarm);
    event BidIntegrityDisputeRejected(uint256 indexed lotId, uint64 indexed seq, bool byTimeout); // byTimeout: cleared by permissionless timeout, not by the arbiter

    // Errors

    // auth / identity
    error Unauthorized();
    error BadSignature();
    error BadNonceKey();
    error WrongSession();
    error WrongLot();
    error EnvelopeExpired();
    error EnvelopeRevoked();

    // funding / escrow
    error WrongDenomination();
    error InsufficientFreeBalance();
    error DepositBelowReserve();
    error NothingToWithdraw();
    error EscrowAlreadyReleased();
    error NoEscrow();

    // config validation (initialize)
    error FeeBpsTooHigh();  // cfg.feeBps or cfg.minIncrementBps exceeds 10_000
    error NoOperatorKeys(); // cfg.operatorQx is empty or its length differs from operatorQy
    error ZeroAddress();    // a fund-routing role in InitConfig is address(0)
    error MaxBidsReached(); // bidIndex is at or above the principal's signed Ceiling.maxBids cap

    // auction
    error NotOpen();
    error AuctionEnded();
    error LotOutlivesSession(); // openLot endsAt must be <= sessionEnd, so every lot's bond-claim deadline stays bounded
    error BidTooLow();

    // attestation
    error BadAttestationSig();
    error WrongMeasurement();
    error QuoteNonceUsed();
    error UnknownOperator(); // operator key is unregistered or revoked
    error StalePrevTop();    // observedPrevTop in the bid does not match the lot's current highBid

    // anti-collusion
    error AcWindowOpen();
    error AcWindowClosed();
    error NotHammered();
    error NotPromotable();
    error NotFlagged();
    error BadCandidate();
    error SessionIsVoided();

    // delivery settlement
    error WrongDeliveryState();
    error DeliveryWindowNotElapsed();
    error DisputeWindowNotElapsed();
    error DisputeWindowElapsed();
    error AlreadyDisputed();
    error WrongBond();

    // integrity dispute
    error CommitmentMismatch();
    error NotOverCeiling();
    error NotPrincipal();
    error IntegrityWindowClosed(); // challenge after _challengeCloseAt, or resolve after openedAt + integrityTimeout
    error NotNonLive();            // lot is not a valid operator-non-liveness target: it has a bid, has no funded intent, or is in the wrong phase
    error BidIntegrityDisputeIsOpen();
    error WindowOpen();
    error WrongSeq();        // reveal seq does not match lot.winnerSeq

    // Lifecycle: configure, open lots, manage the operator key set.
    function initialize(InitConfig calldata cfg) external;
    function openLot(uint256 lotId, address seller, uint96 reservePrice, uint64 endsAt) external;
    function registerOperatorKey(bytes32 qx, bytes32 qy) external returns (bytes32 keyId);
    function revokeOperatorKey(bytes32 keyId) external;
    function isOperatorActive(bytes32 keyId) external view returns (bool);

    // Funding: per-lot ceiling deposits and pull-payment withdrawals.
    function depositCeiling(uint256 lotId, uint256 amount) external payable;
    function withdrawDeposit(uint256 lotId, uint256 amount) external;
    function withdrawableFree(uint256 lotId, address principal) external view returns (uint256);
    function claimPending() external;

    // Bidding: the single canonical entry point for placing a bid.
    function placeBid(
        Ceiling calldata c,
        uint256 lotId,
        address principal,
        uint64 bidIndex,
        uint128 amount,
        bytes calldata signature,
        bytes32 operatorKeyId,
        AttestationQuote calldata quote
    ) external;

    // Hammer, finalize, reveal.
    function hammer(uint256 lotId) external;
    function commitBidBook(uint256 lotId, bytes32 root) external;
    function finalizeWinner(uint256 lotId) external;
    function reveal(uint256 lotId, uint64 seq, uint128 maxBid, bytes32 salt) external;

    // Anti-collusion: void a flagged winner and promote the next clean candidate.
    function voidAndAward(
        uint256 lotId,
        bytes32[] calldata flagInclusionProof,
        NextCleanCandidate calldata candidate
    ) external;
    function voidSession(string calldata reason) external;
    function withdrawRefund(uint256 lotId) external;

    // Delivery-confirmation settlement: deliver, confirm, release, refund, dispute.
    function markDelivered(uint256 lotId, bytes32 deliveryProofHash, string calldata deliveryCid) external;
    function confirmReceipt(uint256 lotId, bytes32 photoHash, string calldata photoCid) external;
    function releaseAfterWindow(uint256 lotId) external;
    function reclaimUndelivered(uint256 lotId) external;
    function openDispute(uint256 lotId, bytes32 claimRef) external payable;
    function resolveDispute(uint256 lotId, Resolution res, bytes32 photoHash) external;

    function getLot(uint256 lotId) external view returns (Lot memory);
    function pendingWithdrawal(address account) external view returns (uint256);

    // Bid-integrity disputes: challenge a bid over its ceiling or with a bad attestation.
    function challengeOverCeiling(uint256 lotId, uint64 seq, uint128 maxBid, bytes32 salt) external;
    function challengeAttestation(uint256 lotId, uint64 seq, bytes calldata evidence) external payable;
    function resolveBidIntegrityDispute(uint256 lotId, uint64 seq, bool upheld, uint128 provenHarm) external;
    function timeoutBidIntegrityDispute(uint256 lotId, uint64 seq) external;
    function slashNonLivenessForLot(uint256 lotId) external; // arbiter only; slashes the operator pool for a funded lot that drew no bid
    function bidIntegrityDisputeOpen(uint256 lotId) external view returns (bool);

    // Pause.
    function pause() external;
    function unpause() external;

    // Envelope revocation: a principal cancels an unused bid nonce key.
    function cancelEnvelope(uint192 nonceKey) external;
    function envelopeCancelled(address principal, uint192 key) external view returns (bool);
}
