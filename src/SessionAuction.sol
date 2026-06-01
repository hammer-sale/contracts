// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Per-session blind-auction clone. Deployed once as a locked implementation (constructor calls
// _disableInitializers), then cloned per session and configured via initialize. Covers configuration,
// funding/escrow, bidding, hammer/finalize/reveal, anti-collusion voiding, two-phase delivery escrow,
// bid-integrity slashing, and pause/envelope revocation.
//
// Every fund path follows checks-effects-interactions under ReentrancyGuardTransient; outbound payments
// are pull-over-push (a failed push is credited for later claim, never reverting the whole call).

import {Initializable}            from "@openzeppelin/contracts/proxy/utils/Initializable.sol";
import {EIP712}                   from "@openzeppelin/contracts/utils/cryptography/EIP712.sol";
import {NoncesKeyed}              from "@openzeppelin/contracts/utils/NoncesKeyed.sol";
import {Pausable}                 from "@openzeppelin/contracts/utils/Pausable.sol";
import {ReentrancyGuardTransient} from "@openzeppelin/contracts/utils/ReentrancyGuardTransient.sol";
import {SafeERC20}                from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import {IERC20}                   from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {SafeCast}                 from "@openzeppelin/contracts/utils/math/SafeCast.sol";
import {P256}                     from "@openzeppelin/contracts/utils/cryptography/P256.sol";
import {SignatureChecker}         from "@openzeppelin/contracts/utils/cryptography/SignatureChecker.sol";

import {ISessionAuction} from "./interfaces/ISessionAuction.sol";
import {IPaddleRegistry} from "./interfaces/IPaddleRegistry.sol";
import {IFlagRegistry}   from "./interfaces/IFlagRegistry.sol";
import {ITreasury}       from "./interfaces/ITreasury.sol";
import {IOperatorBond}   from "./interfaces/IAgentBond.sol";
import {
    Ceiling,
    AttestationQuote,
    NextCleanCandidate,
    InitConfig,
    Lot,
    LotPhase,
    DeliveryState,
    Deposit,
    Bid,
    OperatorKey,
    Resolution,
    HeapEntry,
    IntegrityDispute,
    CEILING_TYPEHASH
} from "./types/HammerTypes.sol";

contract SessionAuction is
    ISessionAuction,
    Initializable,
    EIP712,
    NoncesKeyed,
    Pausable,
    ReentrancyGuardTransient
{
    using SafeERC20 for IERC20;
    using SafeCast for uint256;

    // Per-clone config, set in initialize. Stored rather than immutable because clones share one
    // implementation and cannot set per-session values in its constructor.

    // Roles.
    address private _hammer;
    address private _settler;
    address private _ops;
    address private _arbiter;
    address private _pauser;

    // Wired contracts.
    address private _paddles;
    address private _flags;
    address private _operatorBond;
    address private _treasury;

    // Money and identity.
    address private _paymentToken; // address(0) == native ETH
    address private _feeRecipient;
    bytes32 private _sessionId;
    uint64  private _sessionStart;
    uint64  private _sessionEnd;
    uint16  private _minIncrementBps;
    uint16  private _feeBps;
    uint32  private _timeBufferSec;
    uint16  private _maxExtensions;
    uint32  private _acChallengeSec;
    uint32  private _sellerDeliverSec;
    uint32  private _disputeWindowSec;
    uint128 private _disputeBondAmt;
    uint128 private _integrityBondAmt;
    uint32  private _integrityTimeoutSec;
    uint32  private _revealDeadlineSec;

    // Pinned TEE measurement; bid blindness rests on this enclave/vendor pin, not on key secrecy.
    bytes32 private _mrEnclave;
    bytes32 private _vendorRoot;
    bool    private _sessionVoided;

    // Operator key set.
    mapping(bytes32 keyId => bool active) private _operatorActive;
    mapping(bytes32 keyId => OperatorKey key) private _operatorKeyOf;                      // qx/qy for P256.verify
    mapping(bytes32 keyId => mapping(bytes32 nonce => bool used)) private _quoteNonceUsed; // attestation replay guard

    // Bid-path stores.
    mapping(uint256 lotId => uint64 seq) private _bidSeq;                  // per-lot bid sequence
    mapping(uint256 lotId => mapping(uint64 seq => Bid)) private _bidOf;   // backs reveal and integrity challenges
    mapping(uint256 lotId => mapping(uint64 seq => bytes32)) private _ceilingCommitOf; // reveal opening target per bid
    mapping(uint256 lotId => HeapEntry[5]) private _topUnflagged;          // top-5 distinct-paddle heap, promotion source for voidAndAward
    mapping(uint256 lotId => mapping(uint64 seq => IntegrityDispute)) private _integrityDispute; // Class B bonded dispute
    mapping(uint256 lotId => mapping(uint64 seq => bool recorded)) private _integrityHarmRecorded; // operator harm recorded at most once per seq

    // Per-lot and per-principal state.
    mapping(uint256 lotId => Lot) private _lots;
    mapping(uint256 lotId => mapping(address principal => Deposit)) private _deposit;
    mapping(uint256 lotId => uint256 count) private _lotDepositCount; // live count of bid-capable principals per lot
    mapping(uint256 lotId => mapping(address principal => bool capable)) private _bidCapable; // currently funded >= reserve
    mapping(address account => uint256) private _pendingWithdrawals;
    mapping(address principal => mapping(uint192 nonceKey => bool)) private _envelopeCancelled;

    modifier onlyHammer() {
        if (msg.sender != _hammer) revert Unauthorized();
        _;
    }
    modifier onlyPauser() {
        if (msg.sender != _pauser) revert Unauthorized();
        _;
    }
    modifier onlySettler() {
        if (msg.sender != _settler) revert Unauthorized();
        _;
    }
    modifier onlySeller(uint256 lotId) {
        if (msg.sender != _lots[lotId].seller) revert Unauthorized();
        _;
    }
    modifier onlyBuyer(uint256 lotId) {
        if (msg.sender != _lots[lotId].highBidder) revert Unauthorized();
        _;
    }
    modifier onlyArbiter() {
        if (msg.sender != _arbiter) revert Unauthorized();
        _;
    }

    /// @custom:oz-upgrades-unsafe-allow constructor
    constructor() EIP712("Hammer", "1") {
        _disableInitializers(); // lock the implementation; clones initialize instead
    }

    /// @inheritdoc ISessionAuction
    function initialize(InitConfig calldata cfg) external initializer {
        if (cfg.feeBps > 10_000 || cfg.minIncrementBps > 10_000) revert FeeBpsTooHigh();

        uint256 nKeys = cfg.operatorQx.length;
        if (nKeys == 0 || nKeys != cfg.operatorQy.length) revert NoOperatorKeys(); // need >= 1 operator key

        // Bonds are held on the Lot as uint96; reject an over-uint96 config up front rather than letting a
        // later SafeCast downcast revert.
        if (cfg.disputeBondAmt > type(uint96).max || cfg.integrityBondAmt > type(uint96).max) revert WrongBond();

        // Fund-routing roles have no setter on a clone; a zero address permanently mis-routes or bricks funds
        // (zero feeRecipient strands ERC-20 fees, zero arbiter bricks every dispute).
        if (cfg.hammer == address(0) || cfg.arbiter == address(0) || cfg.feeRecipient == address(0)
            || cfg.treasury == address(0) || cfg.operatorBond == address(0) || cfg.paddles == address(0)
            || cfg.flags == address(0)) revert ZeroAddress();

        // Require a real forward session window, else bondClaimsCloseAt() lands in the past and the session
        // is instantly closeable.
        if (cfg.sessionEnd <= cfg.sessionStart) revert LotOutlivesSession();

        // A voided lot's voidedAt can land up to acChallengeSec past the lot end, and the integrity-challenge
        // deadline runs for disputeWindowSec, so disputeWindowSec must cover acChallengeSec or a victim could
        // not challenge a promoted (voided) bid in time.
        if (cfg.disputeWindowSec < cfg.acChallengeSec) revert LotOutlivesSession();

        _hammer = cfg.hammer;
        _settler = cfg.settler;
        _ops = cfg.ops;
        _arbiter = cfg.arbiter;
        _pauser = cfg.pauser == address(0) ? cfg.hammer : cfg.pauser; // default pauser to hammer
        _paddles = cfg.paddles;
        _flags = cfg.flags;
        _operatorBond = cfg.operatorBond;
        _treasury = cfg.treasury;
        _paymentToken = cfg.paymentToken;
        _feeRecipient = cfg.feeRecipient;
        _sessionId = cfg.sessionId;
        _sessionStart = cfg.sessionStart;
        _sessionEnd = cfg.sessionEnd;
        _minIncrementBps = cfg.minIncrementBps;
        _feeBps = cfg.feeBps;
        _timeBufferSec = cfg.timeBufferSec;
        _maxExtensions = cfg.maxExtensions;
        _acChallengeSec = cfg.acChallengeSec;
        _sellerDeliverSec = cfg.sellerDeliverSec;
        _disputeWindowSec = cfg.disputeWindowSec;
        _disputeBondAmt = cfg.disputeBondAmt;
        _integrityBondAmt = cfg.integrityBondAmt;
        _integrityTimeoutSec = cfg.integrityTimeoutSec;
        _revealDeadlineSec = cfg.revealDeadlineSec;
        _mrEnclave = cfg.mrEnclave;
        _vendorRoot = cfg.vendorRoot;

        // Register the initial operator key set, keyed by keccak256(qx, qy).
        for (uint256 i; i < nKeys; ++i) {
            bytes32 keyId = keccak256(abi.encode(cfg.operatorQx[i], cfg.operatorQy[i]));
            _operatorActive[keyId] = true;
            _operatorKeyOf[keyId] = OperatorKey(cfg.operatorQx[i], cfg.operatorQy[i]);
        }
    }

    /// @inheritdoc ISessionAuction
    function openLot(uint256 lotId, address seller, uint96 reservePrice, uint64 endsAt)
        external
        onlyHammer
    {
        Lot storage lot = _lots[lotId];

        if (lot.phase != uint8(LotPhase.None)) revert NotOpen(); // already opened

        // A lot must end within the session window so bondClaimsCloseAt() (anchored on _sessionEnd)
        // upper-bounds the latest possible bond claim across every lot in the session.
        if (endsAt > _sessionEnd) revert LotOutlivesSession();

        lot.phase = uint8(LotPhase.Open);
        lot.seller = seller;
        lot.reservePrice = reservePrice;
        lot.endsAt = endsAt;
    }

    /// @inheritdoc ISessionAuction
    function registerOperatorKey(bytes32 qx, bytes32 qy) external onlyHammer returns (bytes32 keyId) {
        keyId = keccak256(abi.encode(qx, qy));
        _operatorActive[keyId] = true;
        _operatorKeyOf[keyId] = OperatorKey(qx, qy);
    }

    /// @inheritdoc ISessionAuction
    function revokeOperatorKey(bytes32 keyId) external onlyHammer {
        _operatorActive[keyId] = false;
    }

    /// @inheritdoc ISessionAuction
    function isOperatorActive(bytes32 keyId) external view returns (bool) {
        return _operatorActive[keyId];
    }

    /// @inheritdoc ISessionAuction
    /// @dev A repeat call tops up `free`. Native rail requires msg.value == amount; ERC-20 requires
    ///      msg.value == 0 and pulls via safeTransferFrom.
    function depositCeiling(uint256 lotId, uint256 amount) external payable nonReentrant {
        Lot storage lot = _lots[lotId];

        if (lot.phase != uint8(LotPhase.Open)) revert NotOpen();

        // No per-call reserve guard: a deposit only funds `free`. The reserve floor is enforced at placeBid
        // (BidTooLow), which keeps incremental top-ups and sub-reserve deposits valid.
        _pull(msg.sender, amount);

        uint256 newFree = uint256(_deposit[lotId][msg.sender].free) + amount;
        _deposit[lotId][msg.sender].free = newFree.toUint128();

        // Track bid-capable principals (free >= reserve) as a live count; withdrawDeposit clears the flag
        // when free drops back below. This stops a deposit-then-withdraw or a sub-reserve deposit from
        // forging bid-intent, so a lot with no real interest stays unslashable for non-liveness.
        if (newFree >= lot.reservePrice && !_bidCapable[lotId][msg.sender]) {
            _bidCapable[lotId][msg.sender] = true;
            unchecked { _lotDepositCount[lotId] += 1; }
        }

        emit CeilingDeposited(lotId, msg.sender, amount, newFree);
    }

    /// @inheritdoc ISessionAuction
    function withdrawDeposit(uint256 lotId, uint256 amount) external nonReentrant {
        Deposit storage d = _deposit[lotId][msg.sender];

        if (amount == 0) revert NothingToWithdraw();
        if (amount > d.free) revert InsufficientFreeBalance();

        d.free = uint256(d.free - amount).toUint128(); // amount <= free, safe

        // Keep the bid-capable count live: dropping below the reserve clears bid-capability, so a
        // deposit-then-withdraw cannot forge funded intent on a lot with no real interest.
        if (_bidCapable[lotId][msg.sender] && d.free < _lots[lotId].reservePrice) {
            _bidCapable[lotId][msg.sender] = false;
            unchecked { _lotDepositCount[lotId] -= 1; }
        }

        _pay(msg.sender, amount);

        emit DepositWithdrawn(lotId, msg.sender, amount);
    }

    /// @inheritdoc ISessionAuction
    function withdrawableFree(uint256 lotId, address principal) external view returns (uint256) {
        return _deposit[lotId][principal].free;
    }

    /// @inheritdoc ISessionAuction
    function claimPending() external nonReentrant {
        uint256 amount = _pendingWithdrawals[msg.sender];
        if (amount == 0) revert NothingToWithdraw();

        _pendingWithdrawals[msg.sender] = 0; // zero before payout (checks-effects-interactions)

        _payOrRevert(msg.sender, amount);

        emit WithdrawalClaimed(msg.sender, amount);
    }

    /// @inheritdoc ISessionAuction
    function getLot(uint256 lotId) external view returns (Lot memory) {
        return _lots[lotId];
    }

    /// @inheritdoc ISessionAuction
    function pendingWithdrawal(address account) external view returns (uint256) {
        return _pendingWithdrawals[account];
    }

    /// @inheritdoc ISessionAuction
    function pause() external onlyPauser {
        _pause();
    }

    /// @inheritdoc ISessionAuction
    function unpause() external onlyPauser {
        _unpause();
    }

    /// @inheritdoc ISessionAuction
    function cancelEnvelope(uint192 nonceKey) external {
        _envelopeCancelled[msg.sender][nonceKey] = true;
        emit EnvelopeCancelled(msg.sender, nonceKey);
    }

    /// @inheritdoc ISessionAuction
    function envelopeCancelled(address principal, uint192 key) external view returns (bool) {
        return _envelopeCancelled[principal][key];
    }

    /// @dev Pull `amount` in from `from`. Native: assert msg.value == amount. ERC-20: assert
    ///      msg.value == 0 and safeTransferFrom. Either mismatch reverts WrongDenomination.
    function _pull(address from, uint256 amount) private {
        if (_paymentToken == address(0)) {
            if (msg.value != amount) revert WrongDenomination();
        } else {
            if (msg.value != 0) revert WrongDenomination();
            IERC20(_paymentToken).safeTransferFrom(from, address(this), amount);
        }
    }

    /// @dev Pay `amount` OUT to `to`, pull-over-push: a failed push is credited to _pendingWithdrawals
    ///      (claimable via claimPending) so a hostile recipient cannot strand the protocol. Native uses a
    ///      gas-capped call; ERC-20 uses trySafeTransfer.
    function _pay(address to, uint256 amount) private {
        if (amount == 0) return;

        if (_paymentToken == address(0)) {
            (bool ok,) = payable(to).call{value: amount, gas: 50_000}("");
            if (!ok) _credit(to, amount);
        } else {
            bool ok = IERC20(_paymentToken).trySafeTransfer(to, amount);
            if (!ok) _credit(to, amount);
        }
    }

    /// @dev Pay or revert (used by claimPending, where crediting-on-failure would loop).
    function _payOrRevert(address to, uint256 amount) private {
        if (_paymentToken == address(0)) {
            (bool ok,) = payable(to).call{value: amount}("");
            if (!ok) revert NothingToWithdraw();
        } else {
            IERC20(_paymentToken).safeTransfer(to, amount);
        }
    }

    function _credit(address to, uint256 amount) private {
        _pendingWithdrawals[to] += amount;
        emit WithdrawalCredited(to, amount);
    }

    /// @inheritdoc ISessionAuction
    /// @dev Relayer-agnostic: authorization is the principal's EIP-712 ceiling signature plus a
    ///      1-of-N operator P256 attestation, never msg.sender. The maxBid stays hidden inside ceilingCommit
    ///      and is only opened later at reveal / challenge.
    function placeBid(
        Ceiling calldata c,
        uint256 lotId,
        address principal,
        uint64 bidIndex,
        uint128 amount,
        bytes calldata signature,
        bytes32 operatorKeyId,
        AttestationQuote calldata quote
    ) external whenNotPaused nonReentrant {
        Lot storage lot = _lots[lotId];

        // 1. auction state
        if (lot.phase != uint8(LotPhase.Open)) revert NotOpen();
        if (block.timestamp >= lot.endsAt) revert AuctionEnded();

        // 2. envelope binding (the principal is carried in calldata, never taken from msg.sender)
        if (c.principal != principal) revert Unauthorized();
        if (c.sessionId != _sessionId) revert WrongSession();
        if (c.lotId != lotId) revert WrongLot();
        if (block.timestamp > c.deadline) revert EnvelopeExpired();
        if (_envelopeCancelled[principal][c.nonceKey]) revert EnvelopeRevoked();
        if (c.nonceKey != uint192(uint256(keccak256(abi.encode(_sessionId, lotId, principal))))) revert BadNonceKey();

        // 3. ceiling signature (EOA via ECDSA or smart wallet via ERC-1271)
        bytes32 ceilingDigest = _hashTypedDataV4(
            keccak256(
                abi.encode(
                    CEILING_TYPEHASH, c.principal, c.sessionId, c.lotId, c.ceilingCommit, c.strategy, c.deadline, c.maxBids, c.nonceKey
                )
            )
        );
        if (!SignatureChecker.isValidSignatureNowCalldata(principal, ceilingDigest, signature)) revert BadSignature();

        // 4. consume the envelope keyed nonce BEFORE the attestation checks, so a replayed or out-of-order
        //    bidIndex reverts InvalidAccountNonce rather than StalePrevTop.
        if (bidIndex >= c.maxBids) revert MaxBidsReached(); // enforce the principal's signed bid cap
        _useCheckedNonce(principal, c.nonceKey, bidIndex);

        // 5. attestation: operator active, measurement pin, P256 over the action digest, fresh observedPrevTop,
        //    unused quote nonce
        if (!_operatorActive[operatorKeyId]) revert UnknownOperator();
        if (quote.mrEnclave != _mrEnclave || quote.vendorRoot != _vendorRoot) revert WrongMeasurement();

        bytes32 actionDigest = keccak256(
            abi.encode(
                _sessionId, lotId, amount, c.nonceKey, bidIndex, c.ceilingCommit, quote.nonce, quote.mrEnclave, quote.vendorRoot, quote.observedPrevTop
            )
        );
        OperatorKey storage opk = _operatorKeyOf[operatorKeyId];

        if (!P256.verify(actionDigest, quote.r, quote.s, opk.qx, opk.qy)) revert BadAttestationSig();
        if (uint256(quote.observedPrevTop) != uint256(lot.highBid)) revert StalePrevTop();
        if (_quoteNonceUsed[operatorKeyId][quote.nonce]) revert QuoteNonceUsed();

        _quoteNonceUsed[operatorKeyId][quote.nonce] = true;

        // 6. KYC gate: principal must hold a paddle
        uint16 paddleId = IPaddleRegistry(_paddles).paddleOf(principal);
        if (paddleId == 0) revert Unauthorized();

        // 7. minimum bid
        uint256 minBid = lot.highBidder == address(0)
            ? uint256(lot.reservePrice)
            : uint256(lot.highBid) + (uint256(lot.highBid) * _minIncrementBps) / 10_000;
        if (amount < minBid) revert BidTooLow();

        // Also require a strictly higher amount than any standing top: when bps rounds the increment down to
        // 0 for a tiny highBid (highBid * bps < 1e4), a tie-amount bid must not flip the top.
        if (lot.highBidder != address(0) && amount <= lot.highBid) revert BidTooLow();

        // 8. commit: rebalance free <-> committed only, no external transfer (value is conserved on-chain)
        address prevTop = lot.highBidder;
        Deposit storage dNew = _deposit[lotId][principal];
        uint256 avail = uint256(dNew.free) + dNew.committed;

        if (avail < amount) revert InsufficientFreeBalance();

        dNew.free = uint128(avail - amount);
        dNew.committed = amount;

        // Release the outgoing top's committed back to its free (a self-outbid keeps the same slot).
        uint128 prevReleased;

        if (prevTop != address(0) && prevTop != principal) {
            Deposit storage dPrev = _deposit[lotId][prevTop];
            prevReleased = dPrev.committed;
            dPrev.free += prevReleased;
            dPrev.committed = 0;
        }

        // 9. record the placed bid, advance the top, soft-close
        uint64 seq;
        unchecked {
            seq = ++_bidSeq[lotId];
        }
        _bidOf[lotId][seq] = Bid({amount: amount, principal: principal});
        _ceilingCommitOf[lotId][seq] = c.ceilingCommit; // opening target for reveal / challengeOverCeiling
        lot.highBid = amount;
        lot.highBidder = principal;
        lot.paddleId = paddleId;
        lot.winnerSeq = seq;

        // Maintain the top-5 distinct-paddle heap that voidAndAward promotes from.
        _maybeInsertIntoHeap(lotId, HeapEntry({amount: amount, paddleId: paddleId, seq: uint40(seq), bidder: principal}));

        // Soft-close: a bid landing within the buffer window (endsAt - now <= timeBuffer, lower edge
        // inclusive) resets endsAt to now + timeBuffer, up to _maxExtensions times.
        bool extended;

        if (lot.endsAt - uint64(block.timestamp) <= _timeBufferSec && lot.sealedExtensions < _maxExtensions) {
            lot.endsAt = uint64(block.timestamp) + _timeBufferSec;
            unchecked {
                ++lot.sealedExtensions;
            }
            extended = true;
        }

        // Canonical emit order: BidPlaced, TopBidChanged, BidEscrowCommitted, then AuctionExtended.
        emit BidPlaced(lotId, principal, amount, seq);
        emit TopBidChanged(lotId, principal, amount);
        // BidEscrowCommitted arg-5 is the previous top's free balance AFTER this rebalance (their released
        // committed folded back into free), not the released delta: 0 for a fresh top (no prior bidder), and
        // the principal's own post-commit free for a self-outbid (prevTop == principal).
        emit BidEscrowCommitted(lotId, principal, amount, prevTop, prevTop == address(0) ? 0 : _deposit[lotId][prevTop].free);

        if (extended) emit AuctionExtended(lotId, lot.endsAt);
    }

    /// @dev Maintain the top-5 distinct-paddle heap that voidAndAward promotes from. At most one slot per
    ///      paddle: raise in place on a higher same-paddle bid, else replace the smallest slot. Bounded scans
    ///      over the 5 fixed slots.
    function _maybeInsertIntoHeap(uint256 lotId, HeapEntry memory entry) private {
        HeapEntry[5] storage h = _topUnflagged[lotId];

        // One slot per paddle: if this paddle already holds a slot, keep the higher amount.
        for (uint256 i = 0; i < 5; ++i) {
            if (h[i].bidder != address(0) && h[i].paddleId == entry.paddleId) {
                if (entry.amount > h[i].amount) h[i] = entry; // raise in place
                return;
            }
        }

        // Otherwise overwrite the smallest slot, if the new entry is larger.
        uint256 minIdx = 0;
        for (uint256 i = 1; i < 5; ++i) {
            if (h[i].amount < h[minIdx].amount) minIdx = i;
        }

        if (entry.amount > h[minIdx].amount) h[minIdx] = entry;
    }

    // Session-scoped config accessors, read by the Treasury during depositForfeit.
    function paymentToken() external view returns (address) { return _paymentToken; }
    function feeRecipient() external view returns (address) { return _feeRecipient; }
    function arbiter() external view returns (address) { return _arbiter; }
    function sessionId() external view returns (bytes32) { return _sessionId; } // the operator bond binds a clone to this

    /// @notice Deadline after which no new bid-integrity challenge may open; both challengeOverCeiling
    ///         (Class A) and challengeAttestation (Class B) revert IntegrityWindowClosed past it. Equals the
    ///         latest a lot can end (_sessionEnd plus the max anti-snipe extension,
    ///         _maxExtensions * _timeBufferSec) plus _disputeWindowSec.
    function _challengeCloseAt() internal view returns (uint256) {
        return uint256(_sessionEnd) + uint256(_maxExtensions) * uint256(_timeBufferSec) + uint256(_disputeWindowSec);
    }

    /// @notice Timestamp after which no operator-bond claim can be recorded for this session. The operator
    ///         bond reads it to gate its permissionless closeSession, so the bond neither unlocks before a
    ///         victim's harm can land nor stays locked forever. The latest possible recordClaim is a Class B
    ///         uphold, which must resolve within openedAt + _integrityTimeoutSec and cannot open past
    ///         _challengeCloseAt(); hence this value. closeSession must be strictly past it (> not >=) to
    ///         close the same-block resolve/close race.
    function bondClaimsCloseAt() external view returns (uint256) {
        return _challengeCloseAt() + uint256(_integrityTimeoutSec);
    }

    /// @inheritdoc ISessionAuction
    function hammer(uint256 lotId) external {
        Lot storage lot = _lots[lotId];

        if (lot.phase != uint8(LotPhase.Open)) revert NotOpen();
        if (block.timestamp < lot.endsAt) revert WindowOpen();

        // No qualifying bid: terminal no-sale, no winner.
        if (lot.highBidder == address(0) || lot.highBid < lot.reservePrice) {
            lot.phase = uint8(LotPhase.NoSale);
            emit NoSale(lotId);
            return;
        }

        lot.phase = uint8(LotPhase.Hammered);
        lot.hammeredAt = uint40(block.timestamp);
        lot.escrowAmount = lot.highBid;                 // move the winning bid committed -> escrow
        _deposit[lotId][lot.highBidder].committed = 0;  // the bid now lives in lot.escrowAmount

        emit Hammered(lotId, lot.highBidder, lot.highBid);
    }

    /// @inheritdoc ISessionAuction
    function commitBidBook(uint256 lotId, bytes32 root) external onlySettler {
        Lot storage lot = _lots[lotId];

        if (lot.phase != uint8(LotPhase.Hammered)) revert NotHammered();

        lot.bidBookRoot = root;

        emit BidBookCommitted(lotId, root);
    }

    /// @inheritdoc ISessionAuction
    /// @dev State-only transition into the delivery phase; moves no money (escrow stays held until _release).
    function finalizeWinner(uint256 lotId) external nonReentrant whenNotPaused {
        Lot storage lot = _lots[lotId];

        if (lot.phase != uint8(LotPhase.Hammered) && lot.phase != uint8(LotPhase.Voided)) revert NotHammered();
        if (lot.escrowAmount == 0) revert NoEscrow(); // never strand the winner by finalizing a zeroed escrow

        // Combined gate (reverts AcWindowOpen on either failure): the anti-collusion challenge time must have
        // passed AND the winner must have revealed (or the reveal deadline lapsed). A Voided lot anchors both
        // windows on voidedAt (the promoted winner's window), not the offender's hammeredAt.
        uint256 acAnchor = lot.phase == uint8(LotPhase.Voided) ? uint256(lot.voidedAt) : uint256(lot.hammeredAt);
        bool acClosed = block.timestamp >= acAnchor + _acChallengeSec;
        bool revealOk = lot.revealed || block.timestamp > acAnchor + _revealDeadlineSec;

        if (!acClosed || !revealOk) revert AcWindowOpen();
        if (lot.bidIntegrityOpen != 0) revert BidIntegrityDisputeIsOpen();

        lot.phase = uint8(LotPhase.Awaiting);
        lot.deliveryState = uint8(DeliveryState.AwaitingDelivery);
        lot.awaitingAt = uint40(block.timestamp);

        emit WinnerFinalized(lotId, lot.highBidder, lot.highBid);
    }

    /// @inheritdoc ISessionAuction
    /// @dev The winning principal opens their own commitment (maxBid, salt); sets the reveal gate.
    function reveal(uint256 lotId, uint64 seq, uint128 maxBid, bytes32 salt) external {
        Lot storage lot = _lots[lotId];

        if (seq != lot.winnerSeq) revert WrongSeq();
        // Check CommitmentMismatch before NotPrincipal: an empty-slot reveal (commit is bytes32(0)) surfaces
        // CommitmentMismatch, and only a correct opening by a non-principal surfaces NotPrincipal.
        if (keccak256(abi.encode(maxBid, salt)) != _ceilingCommitOf[lotId][seq]) revert CommitmentMismatch();
        if (msg.sender != _bidOf[lotId][seq].principal) revert NotPrincipal();

        lot.revealed = true;
    }

    /// @inheritdoc ISessionAuction
    /// @dev Permissionless (the merkle proof against the signed flag root is the gate), but whenNotPaused.
    ///      Snapshots and zeroes the offender's escrow before any lot mutation, promotes the next-clean
    ///      candidate (the callee mutates the lot), then routes the forfeit to the Treasury.
    function voidAndAward(
        uint256 lotId,
        bytes32[] calldata flagInclusionProof,
        NextCleanCandidate calldata candidate
    ) external nonReentrant whenNotPaused {
        Lot storage lot = _lots[lotId];

        // 1. void only a provisional winner, only inside the anti-collusion window (anchored at frozen
        //    hammeredAt).
        if (lot.phase != uint8(LotPhase.Hammered)) revert NotHammered();
        if (block.timestamp >= uint256(lot.hammeredAt) + _acChallengeSec) revert AcWindowClosed();

        // 2. prove the current winner's paddle is flagged.
        if (!IFlagRegistry(_flags).verifyMembership(_sessionId, lot.paddleId, flagInclusionProof)) revert NotFlagged();

        // 3. snapshot + zero the offender's escrow before promotion re-locks the slot.
        address offender = lot.highBidder;
        uint128 offenderEscrow = _captureForfeit(lotId);
        address seller = lot.seller; // capture before the helper, which does not overwrite seller

        // 4. promote the next-clean candidate (mutates lot, re-locks, emits LotVoided).
        _verifyAndPromote(lotId, offender, candidate);

        // 5. route the snapshotted forfeit to the Treasury waterfall (both rails).
        _routeForfeit(lotId, offender, offenderEscrow, candidate.amount, seller);
    }

    /// @dev Snapshot + zero the offender's post-hammer escrow (lot.escrowAmount) and return it. Must run
    ///      before _verifyAndPromote, which re-locks the promoted amount into the same slot.
    function _captureForfeit(uint256 lotId) private returns (uint128 offenderEscrow) {
        Lot storage lot = _lots[lotId];
        offenderEscrow = lot.escrowAmount;
        lot.escrowAmount = 0;
    }

    /// @dev Promote the highest unflagged top-5 candidate: verify the named slot is clean and every
    ///      strictly-higher slot is flagged (so the canonical next-clean bid wins), re-lock the promoted
    ///      bidder's own deposit, write the lot, re-bind winnerSeq, lock escrow, and emit the true offender.
    function _verifyAndPromote(uint256 lotId, address offender, NextCleanCandidate calldata c) private {
        HeapEntry[5] storage h = _topUnflagged[lotId];
        uint8 idx = c.heapIndex;

        if (idx >= 5) revert BadCandidate();

        HeapEntry memory e = h[idx];

        if (e.bidder != c.bidder || e.amount != c.amount || e.paddleId != c.paddleId || e.seq != c.seq) revert BadCandidate();
        if (e.bidder == address(0) || e.amount == 0) revert NotPromotable();

        // The promoted paddle must NOT be flagged (a bogus proof fails against the root).
        if (!IFlagRegistry(_flags).verifyNonMembership(_sessionId, e.paddleId, c.flagNonMembership)) revert BadCandidate();

        // Every strictly-higher heap slot must BE flagged (cannot skip a higher clean bid).
        uint256 k;
        for (uint256 i = 0; i < 5; ++i) {
            if (h[i].amount > e.amount) {
                if (!IFlagRegistry(_flags).verifyMembership(_sessionId, h[i].paddleId, c.precedingFlagInclusion[k])) revert BadCandidate();
                unchecked { ++k; }
            }
        }

        // Re-lock the promoted bidder's own deposit: they pay their own bid, no windfall.
        _relockPromoted(lotId, e.bidder, e.amount);

        Lot storage lot = _lots[lotId];
        lot.highBidder = e.bidder;
        lot.highBid    = e.amount;
        lot.paddleId   = e.paddleId;
        lot.voidedAt   = uint40(block.timestamp);
        lot.phase      = uint8(LotPhase.Voided);
        lot.winnerSeq  = e.seq; // re-bind the reveal/challenge target to the promoted winning bid
        lot.revealed   = false; // clear the prior winner's reveal; the promoted winner must open its own commit

        _lockEscrow(lotId, e.bidder, e.amount);

        emit LotVoided(lotId, offender, e.bidder, e.amount); // emit the true offender (passed in), never e.bidder
    }

    /// @dev The promoted next-clean bidder pays their own held bid (free -> committed); reverts
    ///      InsufficientFreeBalance if they withdrew their slack below the bid (no windfall).
    function _relockPromoted(uint256 lotId, address promoted, uint128 promotedAmount) private {
        Deposit storage d = _deposit[lotId][promoted];

        if (d.free < promotedAmount) revert InsufficientFreeBalance();

        d.free -= promotedAmount;
        d.committed += promotedAmount;
    }

    /// @dev On promotion: set lot.escrowAmount to the winning bid and move the winner's committed into it.
    function _lockEscrow(uint256 lotId, address winner, uint128 amount) private {
        _lots[lotId].escrowAmount = amount;
        _deposit[lotId][winner].committed = 0;
    }

    /// @dev Route the snapshotted offender forfeit to the Treasury waterfall (the only cross-contract money
    ///      move in the void path). offenderEscrow is passed as both forfeitAmount and offenderClearing
    ///      because for a void the snapshotted forfeit equals the offender's clearing price.
    function _routeForfeit(uint256 lotId, address offender, uint128 offenderEscrow, uint128 promotedPrice, address seller) private {
        if (offenderEscrow == 0) return;

        address promotedWinner = _lots[lotId].highBidder; // set by _verifyAndPromote

        if (_paymentToken == address(0)) {
            ITreasury(_treasury).depositForfeit{value: offenderEscrow}(
                offender, promotedWinner, lotId, offenderEscrow, offenderEscrow, promotedPrice, seller
            );
        } else {
            IERC20(_paymentToken).forceApprove(_treasury, offenderEscrow); // pre-approve Treasury
            ITreasury(_treasury).depositForfeit(
                offender, promotedWinner, lotId, offenderEscrow, offenderEscrow, promotedPrice, seller
            );
        }
    }

    /// @inheritdoc ISessionAuction
    function voidSession(string calldata reason) external onlyHammer {
        _sessionVoided = true; // O(1) flag: per-(principal,lot) refunds become pull-based via withdrawRefund
        emit SessionVoided(_sessionId, reason);
    }

    /// @inheritdoc ISessionAuction
    /// @dev Pull refund per (principal, lot). Under a session void it returns the caller's deposit
    ///      (free + committed) and, for the winner, lot.escrowAmount, and, for a dispute opener,
    ///      lot.disputeBond. Also serves the Refunded delivery terminal. O(1), checks-effects-interactions.
    function withdrawRefund(uint256 lotId) external nonReentrant {
        if (!_sessionVoided && !_isTerminalRefundable(_lots[lotId].phase)) revert SessionIsVoided();

        Lot storage lot = _lots[lotId];

        // Deposit refund for every caller (losing population plus the winner's slack).
        Deposit storage d = _deposit[lotId][msg.sender];
        uint256 amount = uint256(d.free) + uint256(d.committed);
        d.free = 0;
        d.committed = 0; // zero before payout (checks-effects-interactions)

        // Under a session void the winner also reclaims escrow; this drives the lot to Refunded so a later
        // _release/_refund cannot double-pay (escrowAmount becomes 0).
        uint256 escrow;

        if (_sessionVoided && msg.sender == lot.highBidder && lot.escrowAmount != 0) {
            escrow = lot.escrowAmount;
            lot.escrowAmount  = 0;
            lot.deliveryState = uint8(DeliveryState.Refunded);
            lot.phase         = uint8(LotPhase.Refunded);
            amount += escrow;
        }

        // Under a session void the dispute opener reclaims their full bond (the void is not their fault).
        // resolveDispute zeroes the same slot first, so the two paths never double-pay.
        if (_sessionVoided && msg.sender == lot.disputeOpener && lot.disputeBond != 0) {
            amount += lot.disputeBond;
            lot.disputeBond = 0; // zero before payout (checks-effects-interactions)
        }

        if (amount == 0) revert NothingToWithdraw();

        _pay(msg.sender, amount);

        emit DepositWithdrawn(lotId, msg.sender, amount);
        if (escrow != 0) emit Refunded(lotId, msg.sender, escrow); // winner-escrow refund
    }

    /// @dev A Refunded lot lets withdrawRefund serve the honest no-strand exit even without a session void.
    function _isTerminalRefundable(uint8 phase) private pure returns (bool) {
        return phase == uint8(LotPhase.Refunded);
    }

    // Two-phase delivery escrow. Settlement is not immediate at hammer: the winner escrow stays locked under
    // the DeliveryState machine until exactly one terminal (release or refund) fires. None of these paths is
    // whenNotPaused, because in-flight escrow must always be able to resolve.

    /// @inheritdoc ISessionAuction
    function markDelivered(uint256 lotId, bytes32 deliveryProofHash, string calldata deliveryCid)
        external
        onlySeller(lotId)
    {
        Lot storage lot = _lots[lotId];

        if (lot.phase != uint8(LotPhase.Awaiting) || lot.deliveryState != uint8(DeliveryState.AwaitingDelivery)) {
            revert WrongDeliveryState();
        }

        lot.deliveryProofHash = deliveryProofHash; // gates the transition; the chain stores but never verifies media
        lot.deliveredAt = uint40(block.timestamp);  // dispute-window anchor
        lot.deliveryState = uint8(DeliveryState.Delivered);

        emit Delivered(lotId, deliveryProofHash, deliveryCid);
    }

    /// @inheritdoc ISessionAuction
    function confirmReceipt(uint256 lotId, bytes32 photoHash, string calldata photoCid)
        external
        onlyBuyer(lotId)
        nonReentrant
    {
        if (_lots[lotId].deliveryState != uint8(DeliveryState.Delivered)) revert WrongDeliveryState();

        emit Confirmed(lotId, photoHash, photoCid); // photo reference is event-only (gates nothing)

        _release(lotId);
    }

    /// @inheritdoc ISessionAuction
    function releaseAfterWindow(uint256 lotId) external nonReentrant {
        Lot storage lot = _lots[lotId];

        if (lot.deliveryState != uint8(DeliveryState.Delivered)) revert WrongDeliveryState();
        if (block.timestamp < uint256(lot.deliveredAt) + _disputeWindowSec) revert DisputeWindowNotElapsed();

        emit DeliveryAutoReleased(lotId, lot.seller);

        _release(lotId);
    }

    /// @inheritdoc ISessionAuction
    function reclaimUndelivered(uint256 lotId) external onlyBuyer(lotId) nonReentrant {
        Lot storage lot = _lots[lotId];

        if (lot.phase != uint8(LotPhase.Awaiting) || lot.deliveryState != uint8(DeliveryState.AwaitingDelivery)) {
            revert WrongDeliveryState();
        }
        if (block.timestamp < uint256(lot.awaitingAt) + _sellerDeliverSec) revert DeliveryWindowNotElapsed();

        emit ReclaimedUndelivered(lotId, lot.highBidder, lot.escrowAmount);

        _refund(lotId);
    }

    /// @inheritdoc ISessionAuction
    function openDispute(uint256 lotId, bytes32 claimRef) external payable nonReentrant {
        Lot storage lot = _lots[lotId];

        if (msg.sender != lot.highBidder && msg.sender != lot.seller) revert Unauthorized();

        uint8 ds = lot.deliveryState;

        // Check AlreadyDisputed before the bond pull: a second open on a Disputed lot must not re-pull a
        // bond or overwrite disputeOpener.
        if (ds == uint8(DeliveryState.Disputed)) revert AlreadyDisputed();
        if (ds != uint8(DeliveryState.AwaitingDelivery) && ds != uint8(DeliveryState.Delivered)) {
            revert WrongDeliveryState();
        }
        if (ds == uint8(DeliveryState.Delivered) && block.timestamp >= uint256(lot.deliveredAt) + _disputeWindowSec) {
            revert DisputeWindowElapsed(); // cannot dispute after the auto-release window has lapsed
        }

        // Bond denomination is bond-specific (WrongBond), distinct from _pull's generic WrongDenomination:
        // native must carry exactly the bond as msg.value; ERC-20 must carry zero msg.value.
        if (_paymentToken == address(0)) {
            if (msg.value != _disputeBondAmt) revert WrongBond();
        } else if (msg.value != 0) {
            revert WrongBond();
        }

        _pull(msg.sender, _disputeBondAmt); // native re-asserts msg.value == bond; ERC-20 does safeTransferFrom

        lot.disputeOpener = msg.sender;
        lot.disputeBond = uint96(_disputeBondAmt); // init-bounded <= type(uint96).max (WrongBond at init)
        lot.disputeRef = claimRef;
        lot.deliveryState = uint8(DeliveryState.Disputed); // escrow now frozen until resolveDispute

        emit DisputeOpened(lotId, msg.sender, _disputeBondAmt, claimRef);
    }

    /// @inheritdoc ISessionAuction
    function resolveDispute(uint256 lotId, Resolution res, bytes32 photoHash)
        external
        onlyArbiter
        nonReentrant
    {
        Lot storage lot = _lots[lotId];

        if (lot.deliveryState != uint8(DeliveryState.Disputed)) revert WrongDeliveryState();

        photoHash; // arbiter evidence reference: event/context only, gates nothing

        // The bond goes to the winning party: the opener if its position won, else the honest counterparty.
        address bondRecipient = (res == Resolution.ReleaseToSeller)
            ? (lot.disputeOpener == lot.seller ? lot.disputeOpener : lot.seller)
            : (lot.disputeOpener == lot.highBidder ? lot.disputeOpener : lot.highBidder);
        uint256 bond = lot.disputeBond;
        lot.disputeBond = 0; // zero first (checks-effects-interactions); _release/_refund each zero escrow before their _pay

        if (res == Resolution.ReleaseToSeller) {
            _release(lotId);
        } else {
            _refund(lotId);
        }

        if (bond != 0) _pay(bondRecipient, bond);

        emit DisputeResolved(lotId, res, bondRecipient);
    }

    // Escrow terminals: the only exits that move escrow out.

    /// @dev Pay the seller (escrow minus fee) and the fee recipient; the sole seller-paying terminal.
    ///      The integrity gate and the zeroing precede every _pay, so a reentrant call sees zero escrow and
    ///      reverts NoEscrow.
    function _release(uint256 lotId) internal {
        Lot storage lot = _lots[lotId];
        uint256 amount = lot.escrowAmount;

        if (amount == 0) revert NoEscrow();                       // no-double-pay guard
        if (lot.bidIntegrityOpen != 0) revert BidIntegrityDisputeIsOpen(); // an open Class B dispute freezes release

        lot.escrowAmount = 0;                                     // effects first
        lot.deliveryState = uint8(DeliveryState.Released);
        lot.phase = uint8(LotPhase.Settled);

        uint256 fee = _feeOf(amount);
        uint256 proceeds = amount - fee;                          // truncation dust stays with the seller

        _pay(lot.seller, proceeds);                               // interactions
        if (fee != 0) _pay(_feeRecipient, fee);
        emit Released(lotId, lot.seller, proceeds, fee);
    }

    /// @dev Refund the full escrow to the buyer with no fee (there is no completed sale).
    function _refund(uint256 lotId) internal {
        Lot storage lot = _lots[lotId];
        uint256 amount = lot.escrowAmount;

        if (amount == 0) revert NoEscrow();

        lot.escrowAmount = 0;                                     // effects first
        lot.deliveryState = uint8(DeliveryState.Refunded);
        lot.phase = uint8(LotPhase.Refunded);

        _pay(lot.highBidder, amount);                            // interactions: full escrow, no fee
        emit Refunded(lotId, lot.highBidder, uint128(amount));
    }

    /// @dev Truncating settlement fee, floor(gross * _feeBps / 10_000). gross is a uint128 escrow and
    ///      _feeBps <= 10_000, so the product never overflows uint256; dust stays with the seller.
    function _feeOf(uint256 gross) internal view returns (uint256) {
        return (gross * _feeBps) / 10_000;
    }

    // Bid-integrity challenges (Class A self-proving, Class B bonded).

    /// @inheritdoc ISessionAuction
    /// @dev Class A (self-proving): the bid's principal opens their committed ceiling and proves the placed
    ///      bid exceeded it (the operator over-bid the cap). Records the harm into the operator bond
    ///      atomically; posts no bond, opens no dispute, and never gates _release.
    function challengeOverCeiling(uint256 lotId, uint64 seq, uint128 maxBid, bytes32 salt) external nonReentrant {
        // A claim cannot open after the challenge deadline, keeping the bond-claim deadline an upper bound
        // (no claim lands after operators may withdraw their bond).
        if (block.timestamp > _challengeCloseAt()) revert IntegrityWindowClosed();

        Bid storage b = _bidOf[lotId][seq];

        if (msg.sender != b.principal) revert NotPrincipal();
        if (keccak256(abi.encode(maxBid, salt)) != _ceilingCommitOf[lotId][seq]) revert CommitmentMismatch();
        if (b.amount <= maxBid) revert NotOverCeiling();
        if (_integrityHarmRecorded[lotId][seq]) revert AlreadyDisputed(); // harm recorded once per seq

        _integrityHarmRecorded[lotId][seq] = true;
        uint128 provenHarm = b.amount - maxBid; // the over-ceiling excess

        emit BidIntegrityDisputeOpened(lotId, seq, msg.sender, 0, 0); // Class A is class 0, no bond
        IOperatorBond(_operatorBond).recordClaim(_sessionId, b.principal, provenHarm);
        emit BidIntegrityClaimUpheld(lotId, seq, b.principal, provenHarm);
    }

    /// @inheritdoc ISessionAuction
    /// @dev Class B (bonded, resolved by the arbiter or by timeout): posts a refundable _integrityBondAmt
    ///      and opens a gated dispute (bidIntegrityOpen++, which freezes _release) pending the arbiter or
    ///      the timeout.
    function challengeAttestation(uint256 lotId, uint64 seq, bytes calldata /*proof*/)
        external
        payable
        nonReentrant
    {
        // A dispute cannot open after the challenge deadline; one opened right at the deadline still resolves
        // or times out within _integrityTimeoutSec, i.e. by bondClaimsCloseAt().
        if (block.timestamp > _challengeCloseAt()) revert IntegrityWindowClosed();
        if (_bidOf[lotId][seq].principal == address(0)) revert NotPrincipal(); // unknown seq (never placed)

        IntegrityDispute storage d = _integrityDispute[lotId][seq];

        if (d.open) revert AlreadyDisputed(); // one open Class B dispute per seq

        // Bond denomination (WrongBond): native carries exactly the bond; ERC-20 carries zero msg.value.
        if (_paymentToken == address(0)) {
            if (msg.value != _integrityBondAmt) revert WrongBond();
        } else if (msg.value != 0) {
            revert WrongBond();
        }

        _pull(msg.sender, _integrityBondAmt);

        d.challenger = msg.sender;
        d.bond = uint96(_integrityBondAmt); // init-bounded <= type(uint96).max (WrongBond at init)
        d.openedAt = uint40(block.timestamp);
        d.open = true;
        d.class = 1;

        // Class B gate that freezes _release while > 0; checked add so a 256th concurrent open reverts
        // rather than wrapping the counter back to 0 (which would read as clean).
        _lots[lotId].bidIntegrityOpen += 1;

        emit BidIntegrityDisputeOpened(lotId, seq, msg.sender, 1, _integrityBondAmt);
    }

    /// @inheritdoc ISessionAuction
    /// @dev Arbiter-only resolution of a Class B dispute: uphold refunds the bond to the challenger and
    ///      records the harm against the operator bond; reject forfeits the bond to the seller. Either way
    ///      clears the gate (bidIntegrityOpen--). Gate and bond are zeroed before any external move.
    function resolveBidIntegrityDispute(uint256 lotId, uint64 seq, bool upheld, uint128 provenHarm)
        external
        onlyArbiter
        nonReentrant
    {
        IntegrityDispute storage d = _integrityDispute[lotId][seq];

        if (!d.open) revert WrongDeliveryState(); // no open Class B dispute on this seq (Class A / already resolved)

        // The arbiter must resolve within the dispute's timeout; past it only the permissionless
        // timeoutBidIntegrityDispute applies (which records no claim). So the latest upheld recordClaim is at
        // openedAt + _integrityTimeoutSec <= bondClaimsCloseAt(), and closeSession (strictly past that) is safe.
        if (block.timestamp > uint256(d.openedAt) + _integrityTimeoutSec) revert IntegrityWindowClosed();

        address challenger = d.challenger;
        uint256 bond = d.bond;
        d.open = false; // zero first (checks-effects-interactions)
        d.bond = 0;
        unchecked { --_lots[lotId].bidIntegrityOpen; }

        if (upheld) {
            if (!_integrityHarmRecorded[lotId][seq]) { // record harm once per seq (a Class A may have already)
                address victim = _bidOf[lotId][seq].principal;
                // provenHarm passes through uncapped: the arbiter is a fully trusted role that also sets the
                // dispute outcome, so bounding this input would contradict that trust model.
                _integrityHarmRecorded[lotId][seq] = true;
                IOperatorBond(_operatorBond).recordClaim(_sessionId, victim, provenHarm);
                emit BidIntegrityClaimUpheld(lotId, seq, victim, provenHarm);
            }

            if (bond != 0) _pay(challenger, bond); // refund the honest challenger
        } else {
            emit BidIntegrityDisputeRejected(lotId, seq, false);
            if (bond != 0) _pay(_lots[lotId].seller, bond); // forfeit to the seller
        }
    }

    /// @inheritdoc ISessionAuction
    /// @dev Permissionless: after _integrityTimeoutSec a silent (unresolved) Class B dispute auto-resolves
    ///      against the challenger (bond to the seller, byTimeout), so the gate cannot freeze _release
    ///      indefinitely if the arbiter never acts.
    function timeoutBidIntegrityDispute(uint256 lotId, uint64 seq) external nonReentrant {
        IntegrityDispute storage d = _integrityDispute[lotId][seq];

        if (!d.open) revert WrongDeliveryState(); // no open Class B dispute on this seq (Class A / already resolved)
        if (block.timestamp < uint256(d.openedAt) + _integrityTimeoutSec) revert WindowOpen();

        address challenger = d.challenger;
        uint256 bond = d.bond;
        d.open = false; // zero first (checks-effects-interactions)
        d.bond = 0;
        unchecked { --_lots[lotId].bidIntegrityOpen; }

        emit BidIntegrityDisputeRejected(lotId, seq, true);
        // Outside a void a silent challenge loses, bond to the seller. Under a session void the whole lot is
        // unwound (the challenged bid is itself refunded), so a silent timeout is not the challenger's fault:
        // refund the challenger instead. Only this permissionless fallback is void-aware; the arbiter can
        // still resolve upheld within the window to record harm and refund.
        if (bond != 0) _pay(_sessionVoided ? challenger : _lots[lotId].seller, bond);
    }

    /// @inheritdoc ISessionAuction
    /// @dev Operator non-liveness slash: the arbiter slashes the operator pool for a lot that received zero
    ///      bids despite at least one funded ceiling (funded bid-intent), after the auction window plus a
    ///      _disputeWindowSec grace. The guards bound the arbiter so a live operator set is never penalized:
    ///      any landed bid or no funded deposit makes the lot unslashable. Voids the lot (terminal; funded
    ///      principals still reclaim `free` via withdrawDeposit) and flags the session for the slash, whose
    ///      pool routes to the Treasury at settle. Phase is set before the external call.
    function slashNonLivenessForLot(uint256 lotId) external onlyArbiter nonReentrant {
        Lot storage lot = _lots[lotId];

        // No-winner state only: Open (never hammered) or NoSale (hammered with no qualifying bid).
        if (lot.phase != uint8(LotPhase.Open) && lot.phase != uint8(LotPhase.NoSale)) revert NotNonLive();
        if (block.timestamp < uint256(lot.endsAt) + _disputeWindowSec) revert WindowOpen(); // auction window + grace
        if (lot.highBidder != address(0)) revert NotNonLive(); // a bid landed: operators were live
        if (_lotDepositCount[lotId] == 0) revert NotNonLive(); // no funded intent: no interest, not operator failure

        lot.phase = uint8(LotPhase.Voided); // effects first: terminal, blocks re-slash; principals' free stays withdrawable

        emit LotNonLivenessSlashed(lotId);

        IOperatorBond(_operatorBond).slashNonLiveness(_sessionId, lotId); // flags the pool, routed to Treasury at settle
    }

    /// @inheritdoc ISessionAuction
    function bidIntegrityDisputeOpen(uint256 lotId) external view returns (bool) {
        return _lots[lotId].bidIntegrityOpen != 0; // packed open-dispute counter (0 == clean)
    }
}
