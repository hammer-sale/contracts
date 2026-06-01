// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Hammer canonical shared types: enums, structs, and CEILING_TYPEHASH.
//
// A bidder's max bid is never stored on-chain; it is committed as
// ceilingCommit = keccak256(abi.encode(uint128 maxBid, bytes32 salt)).

enum LotPhase {
    None,        // 0  not opened
    Open,        // 1  accepting bids
    Hammered,    // 2  provisional winner; anti-collusion challenge window open
    Voided,      // 3  flagged winner replaced by next-clean; challenge window still gates finalize
    Awaiting,    // 4  winner final (no void possible); delivery pipeline live
    Settled,     // 5  terminal: escrow released to seller
    Refunded,    // 6  terminal: escrow refunded to buyer (dispute or undelivered)
    NoSale       // 7  terminal: reserve not met or no bids
}

// Fine-grained delivery state, meaningful only once LotPhase reaches Awaiting.
enum DeliveryState {
    None,             // 0  before Awaiting
    AwaitingDelivery, // 1  set on entry to Awaiting
    Delivered,        // 2  seller marked delivered
    Disputed,         // 3  either party opened a bonded dispute; escrow frozen
    Released,         // 4  terminal (maps to LotPhase.Settled)
    Refunded          // 5  terminal (maps to LotPhase.Refunded)
}

enum Resolution { ReleaseToSeller, RefundToBuyer }

// EIP-712 ceiling typehash and signed envelope.

bytes32 constant CEILING_TYPEHASH = keccak256(
    "Ceiling(address principal,bytes32 sessionId,uint256 lotId,bytes32 ceilingCommit,uint8 strategy,uint64 deadline,uint64 maxBids,uint192 nonceKey)"
);

struct Ceiling {
    address principal;     // the bidder; taken from calldata and bound by signature, never msg.sender
    bytes32 sessionId;     // must equal the clone's SESSION_ID
    uint256 lotId;         // must equal placeBid lotId
    bytes32 ceilingCommit; // keccak256(abi.encode(maxBid, salt)); maxBid never on-chain
    uint8   strategy;      // 0=incremental, 1=snipe, 2=proxy
    uint64  deadline;      // absolute unix; enforced on-chain
    uint64  maxBids;       // sequential bids authorised under nonceKey
    uint192 nonceKey;      // == uint192(uint256(keccak256(abi.encode(sessionId, lotId, principal))))
}

// Attestation quote carried per bid. On-chain verification covers only the leaf signature
// and the pinned measurement; cert-chain freshness and revocation are checked off-chain.
// s must be low-S normalized (<= HALF_N) or P256.verify rejects the signature.
struct AttestationQuote {
    bytes32 mrEnclave;       // signed into the action digest; must equal the pinned _enclave.mrEnclave (fail closed)
    bytes32 vendorRoot;      // signed into the action digest; must equal the pinned _enclave.vendorRoot
    bytes32 observedPrevTop; // top bid the enclave priced against; signed in and must equal lot.highBid
    bytes32 nonce;           // anti-replay nonce; one-shot per operator key (keyed by (operatorKey, nonce))
    bytes32 r;               // P-256 signature half R over the action digest
    bytes32 s;               // P-256 signature half S, low-S normalized (<= HALF_N)
}

// Candidate promoted to winner when the current top bid is voided. The proofs establish that
// this bid is itself unflagged and that every higher-ranked occupant is flagged, so it is the
// highest clean bid.
struct NextCleanCandidate {
    uint8       heapIndex;             // slot in _topUnflagged[lotId] being promoted
    address     bidder;                // = principal of the next-clean bid
    uint128     amount;
    uint16      paddleId;
    uint40      seq;
    bytes32[]   flagNonMembership;     // proof that this paddleId is not in the flag set
    bytes32[][] precedingFlagInclusion;// proofs that every higher heap slot's paddle is flagged
}

// Per-clone init config. Fields are grouped to pack tightly; the storage layout is fixed.
struct InitConfig {
    address hammer; address settler; address ops; address arbiter; address pauser;
    address paddles; address flags; address operatorBond; address treasury;
    address paymentToken; address feeRecipient;
    bytes32 sessionId; uint64 sessionStart; uint64 sessionEnd;
    uint16 minIncrementBps; uint16 feeBps;
    uint32 timeBufferSec; uint16 maxExtensions;
    uint32 acChallengeSec; uint32 sellerDeliverSec; uint32 disputeWindowSec;
    uint128 disputeBondAmt; uint128 integrityBondAmt; uint32 integrityTimeoutSec;
    uint32 revealDeadlineSec;
    bytes32 mrEnclave; bytes32 vendorRoot;        // pinned enclave measurement; blindness rests here, not on key secrecy
    bytes32[] operatorQx; bytes32[] operatorQy;   // initial operator key set (qx[i], qy[i]); >= 1; extendable via registerOperatorKey
}

// Canonical Lot struct, packed with a fixed slot layout.
struct Lot {
    // slot 0  (30 bytes used, 2 bytes padding) - the hot slot
    uint128 highBid;          // [0:16)   current top bid (becomes winner escrow once final), base units
    uint64  endsAt;           // [16:24)  auction end; only ever extended by soft-close
    uint16  paddleId;         // [24:26)  current top bidder's KYC paddle
    uint16  sealedExtensions; // [26:28)  number of soft-close extensions applied
    uint8   phase;            // [28:29)  LotPhase
    uint8   deliveryState;    // [29:30)  DeliveryState (packed here to avoid a cold SLOAD)

    // slot 1  (20 + 5 + 5 + 1 + 1 = 32 bytes)
    address highBidder;       // [0:20)   = principal (never the enclave or agent executor)
    uint40  hammeredAt;       // [20:25)  set at hammer(); anchors the anti-collusion challenge window
    uint40  voidedAt;         // [25:30)  set at voidAndAward(); 0 if not voided
    bool    revealed;         // [30:31)  set by reveal() for the winning bid; gates finalize
    uint8   bidIntegrityOpen; // [31:32)  count of open bid-integrity disputes; 0 == clean

    // slot 2
    address seller;           // [0:20)
    uint40  awaitingAt;       // [20:25)  set at finalizeWinner(); anchors the seller-deliver window
    uint40  deliveredAt;      // [25:30)  set at markDelivered(); anchors the dispute window

    // slot 3
    uint96  reservePrice;     // [0:12)   base units
    uint128 escrowAmount;     // [12:28)  winner escrow carried into delivery; set at hammer/promote

    // slot 4
    uint64  winnerSeq;        // [0:8)    bid seq of the winning bid; set at hammer, re-set at voidAndAward; 0 == none yet

    // slot 5  (written at commitBidBook)
    bytes32 bidBookRoot;      // post-hammer bid-book merkle root (provenance)

    // slot 6  (written lazily at markDelivered)
    bytes32 deliveryProofHash;// off-chain delivery proof reference; gates the Delivered transition

    // slot 7  (written lazily on dispute)
    address disputeOpener;    // [0:20)   delivery dispute opener (buyer or seller)
    uint96  disputeBond;      // [20:32)  refundable delivery dispute bond, base units

    // slot 8  (written lazily on dispute)
    bytes32 disputeRef;       // off-chain claim reference
}

// Per-(principal, lot) deposit and bid-path stores.

struct Deposit {            // 1 slot
    uint128 free;           // withdrawable any time
    uint128 committed;      // locked behind this principal's current top bid (0 if not top)
}

// Per-(lotId, seq) record of a placed bid; read by reveal and challengeOverCeiling.
struct Bid { uint128 amount; address principal; } // 2 slots

// Anti-collusion heap of the top distinct-paddle bids; each occupant's committed deposit stays held.
struct HeapEntry { uint128 amount; uint16 paddleId; uint40 seq; address bidder; } // 2 slots

// Per-(lotId, seq) record for a bonded bid-integrity dispute resolved by the arbiter or a timeout.
// Self-proving challenges record harm directly into IOperatorBond and write no record here; the
// packed lot.bidIntegrityOpen counter is the gate either way.
struct IntegrityDispute {
    address challenger;  // [0:20)   opener and bond payer
    uint96  bond;        // [20:32)  refundable challenge bond, base units
    uint40  openedAt;    // anchors the timeout: auto-resolves after _integrityTimeoutSec if the arbiter is silent
    bool    open;        // true while gating; cleared by resolveBidIntegrityDispute or the permissionless timeout
    uint8   class;       // dispute class tag; always 1 (bonded, arbiter or timeout)
}

// Pinned TEE attestation measurement that quotes are checked against.
struct EnclaveConfig { bytes32 mrEnclave; bytes32 vendorRoot; }

// Registered operator P-256 public key. keyId == keccak256(abi.encode(qx, qy)).
struct OperatorKey { bytes32 qx; bytes32 qy; }
