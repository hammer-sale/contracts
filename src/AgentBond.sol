// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Concrete IOperatorBond (interfaces/IAgentBond.sol): a per-session economic bond for the registered
// operator set with a real slash distribution. Operators stake per session; upheld harm slashes the
// session pool, paying recorded victims pro-rata (no first-come drain) with the remainder to the Treasury
// sink. A slashed pool is not recoverable by the operators.
//
// Trust surface: onlyAuction keys to the factory-registered clone set; registerClone admits the owner or
// the wired factory, and every entrypoint that takes a clone re-reads its sessionId so a clone for session
// X cannot inflate session Y's ledger.
//
// Fund safety: ReentrancyGuardTransient on every fund-moving exit, CEI (state finalized before value
// leaves), and a gas-capped pull-over-push payout with a pendingWithdrawals credit fallback.
//
// Dual rail: stake is taken on the session's rail, read from the verified clone's paymentToken (native if
// address(0), else that ERC-20). deposit fixes the rail on first deposit; settle, claim, withdraw, and the
// pull-over-push fallback all pay in that token. This singleton custodies one denomination per session,
// isolated, so native and ERC-20 pools coexist.

import {IOperatorBond}   from "./interfaces/IAgentBond.sol";
import {ISessionAuction} from "./interfaces/ISessionAuction.sol";

import {Ownable}                  from "@openzeppelin/contracts/access/Ownable.sol";
import {ReentrancyGuardTransient} from "@openzeppelin/contracts/utils/ReentrancyGuardTransient.sol";
import {IERC20}                   from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {SafeERC20}                from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";

/// @dev Read surface AgentBond needs from a registered clone: its session binding, the bond-claim
///      deadline that gates closeSession, and the paymentToken fixing the bond rail (native if zero).
interface ISessionBondConfig {
    function sessionId() external view returns (bytes32);
    function bondClaimsCloseAt() external view returns (uint256);
    function paymentToken() external view returns (address);
}

contract AgentBond is IOperatorBond, Ownable, ReentrancyGuardTransient {
    using SafeERC20 for IERC20;

    error WrongDenomination(); // deposit must match the session's bond rail (native or its paymentToken)
    error NothingToWithdraw(); // no remaining (unslashed) bond for this caller on this session
    error WindowOpen();        // an unresolved (recorded but unsettled) claim/slash still gates the withdraw
    error NothingToSettle();   // no claims/non-liveness recorded, or the slash pool already settled
    error NothingToClaim();    // no recorded harm for this victim, or already claimed
    error SessionNotClosed();  // settle/withdraw/close gated until the session's bondClaimsCloseAt deadline,
                               // so an operator cannot drain stake before victim harm can land
    error SessionAlreadyClosed(); // ledger sealed once closed; no recordClaim/slashNonLiveness may land
                               // after operators become eligible to withdraw

    event CloneRegistered(address indexed clone);
    event BondDeposited(bytes32 indexed sessionId, address indexed operator, uint256 amount);
    event ClaimRecorded(bytes32 indexed sessionId, address indexed victim, uint128 provenHarm, uint256 totalClaims);
    event SlashSettled(bytes32 indexed sessionId, uint256 toVictims, uint256 toTreasury);
    event SlashClaimed(bytes32 indexed sessionId, address indexed victim, uint256 amount);
    event NonLivenessSlashed(bytes32 indexed sessionId, uint256 lotId, uint256 pooledBond);
    event SessionClosed(bytes32 indexed sessionId); // unlocks settle/withdraw, seals the claim ledger
    event BondWithdrawn(bytes32 indexed sessionId, address indexed operator, uint256 amount);
    event WithdrawalCredited(address indexed token, address indexed account, uint256 amount); // token==0 native
    event WithdrawalClaimed(address indexed token, address indexed account, uint256 amount);

    /// @notice Forfeit sink the slash remainder flows to. Owner-wired post-deploy, since AgentBond is
    ///         constructed with no args and the Treasury address is not known at that point.
    address public treasury;
    /// @notice The Hammer factory, authorized alongside the owner to register a clone.
    address public factory;

    /// @dev Registered clone set the onlyAuction gate keys to.
    mapping(address clone => bool registered) private _isClone;

    struct Pool {
        uint256 bond;          // total staked, less withdrawn/slashed (drops to 0 on a slash)
        uint256 totalClaims;   // sum of recorded provenHarm across upheld victim claims (settle weight)
        uint256 victimsPot;    // amount set aside for victims at settle (claimSlash divides this pot)
        uint256 settledClaims; // totalClaims snapshot at settle (the claimSlash pro-rata divisor)
        bool    nonLiveness;   // non-liveness slash recorded (lets settle run with no victim claims)
        bool    settled;       // true once settleSlash distributed the pool
    }

    mapping(bytes32 sessionId => Pool) private _pools;

    /// @dev Per-(session, operator) stake so each operator withdraws only its own remaining bond.
    mapping(bytes32 sessionId => mapping(address operator => uint256 stake)) private _stakeOf;
    /// @dev Per-(session, victim) recorded harm; settleSlash/claimSlash pay pro-rata by this weight.
    mapping(bytes32 sessionId => mapping(address victim => uint128 harm)) private _harmOf;

    /// @dev True once the session is closed. Gates settleSlash and withdraw (an operator cannot withdraw
    ///      before harm can be recorded) and seals the ledger (recordClaim/slashNonLiveness revert once
    ///      set). Set only by closeSession; never un-set.
    mapping(bytes32 sessionId => bool closed) public sessionClosed;
    /// @dev Running sum of claimSlash payouts per session. A session can never pay victims more than its
    ///      own snapshotted victimsPot, so its payouts can never draw down another session's stake out of
    ///      the shared singleton balance.
    mapping(bytes32 sessionId => uint256 paid) public claimedFromPot;

    /// @dev Bond rail per session, fixed on first deposit from the clone's paymentToken (address(0) =
    ///      native, else the ERC-20). settle/claim/withdraw all pay in this token. `_bondTokenSet`
    ///      distinguishes a native session (token == 0) from an un-deposited one.
    mapping(bytes32 sessionId => address token) public sessionToken;
    mapping(bytes32 sessionId => bool set) private _bondTokenSet;

    /// @dev Failed-push credits (the pull half of the pull-over-push payout), keyed by token so a native
    ///      and an ERC-20 session never alias the same credit slot. token == address(0) is native.
    mapping(address token => mapping(address account => uint256 amount)) public pendingWithdrawals;

    modifier onlyAuction() {
        if (!_isClone[msg.sender]) revert ISessionAuction.Unauthorized();
        _;
    }

    constructor() Ownable(msg.sender) {}

    function setTreasury(address t) external onlyOwner {
        if (t == address(0)) revert ISessionAuction.ZeroAddress(); // remainder sink cannot be zero (a _pay to 0 would burn)
        treasury = t;
    }

    function setFactory(address f) external onlyOwner {
        if (f == address(0)) revert ISessionAuction.ZeroAddress();
        factory = f;
    }

    /// @notice Seal a session, unlocking settleSlash + withdraw and freezing the claim ledger (recordClaim
    ///         and slashNonLiveness revert once closed). Permissionless but gated two ways:
    ///         - reverts until the session's own bondClaimsCloseAt() (the latest any recordClaim can fire),
    ///           so an operator cannot close-then-drain before victim harm can land;
    ///         - requires a registered clone that owns the passed sessionId, so no caller can close a
    ///           foreign session.
    ///         No early override. Idempotent; never un-set.
    function closeSession(bytes32 sessionId, address clone) external {
        if (!_isClone[clone]) revert ISessionAuction.Unauthorized(); // registered clone only

        ISessionBondConfig c = ISessionBondConfig(clone);
        if (c.sessionId() != sessionId) revert ISessionAuction.Unauthorized(); // clone must own this session

        uint256 deadline = c.bondClaimsCloseAt();

        // A zero/unset deadline (uninitialized clone) can never be "past", so reject explicitly.
        if (deadline == 0) revert SessionNotClosed();

        // Strictly past the deadline (> not >=): a claim can still land AT bondClaimsCloseAt(), so close
        // only after it to avoid sealing the ledger in the same block a claim is recorded.
        if (block.timestamp <= deadline) revert SessionNotClosed();

        sessionClosed[sessionId] = true;
        emit SessionClosed(sessionId);
    }

    /// @inheritdoc IOperatorBond
    /// @dev Admits the owner or the Hammer factory (the in-tx createSession path); an arbitrary EOA is
    ///      rejected. A clone may be registered before init, so its session binding is read live at
    ///      recordClaim time, not here.
    function registerClone(address clone) external {
        if (msg.sender != owner() && msg.sender != factory) revert ISessionAuction.Unauthorized();

        _isClone[clone] = true;
        emit CloneRegistered(clone);
    }

    /// @inheritdoc IOperatorBond
    /// @dev Unified stake entrypoint (native or the session's ERC-20). The caller passes the session's
    ///      `clone` (must be registered and own `sessionId`), so the bond rail is read from its
    ///      paymentToken. Native: token==0, msg.value == amount. ERC-20: msg.value == 0, `amount` pulled
    ///      via safeTransferFrom. Rail fixed on first deposit; every later deposit must match.
    function deposit(bytes32 sessionId, address clone, uint256 amount) external payable nonReentrant {
        if (!_isClone[clone]) revert ISessionAuction.Unauthorized(); // registered clone only
        if (ISessionBondConfig(clone).sessionId() != sessionId) revert ISessionAuction.Unauthorized(); // clone owns session
        if (amount == 0) revert WrongDenomination();

        // Fix the rail on first deposit from the clone's paymentToken; every later deposit must match.
        address token = ISessionBondConfig(clone).paymentToken();

        if (_bondTokenSet[sessionId]) {
            if (sessionToken[sessionId] != token) revert WrongDenomination();
        } else {
            sessionToken[sessionId] = token;
            _bondTokenSet[sessionId] = true;
        }

        uint256 credited;

        if (token == address(0)) {
            if (msg.value != amount) revert WrongDenomination(); // native: value must equal the credited amount
            credited = amount;
        } else {
            if (msg.value != 0) revert WrongDenomination(); // ERC-20: no native value

            // Credit the measured balance delta, not the requested amount, so a fee-on-transfer token
            // cannot over-credit the pool beyond what arrived.
            uint256 balBefore = IERC20(token).balanceOf(address(this));
            IERC20(token).safeTransferFrom(msg.sender, address(this), amount);
            credited = IERC20(token).balanceOf(address(this)) - balBefore;

            if (credited == 0) revert WrongDenomination(); // a zero net transfer funds nothing
        }

        Pool storage p = _pools[sessionId];
        p.bond += credited;
        _stakeOf[sessionId][msg.sender] += credited;

        emit BondDeposited(sessionId, msg.sender, credited);
    }

    /// @inheritdoc IOperatorBond
    /// @dev onlyAuction; caller must be the clone for this session. Adds (victim, provenHarm) so
    ///      settleSlash/claimSlash pay victims pro-rata by total harm (no first-come drain). Harm is summed
    ///      across the victim's distinct (lotId, seq) events; the caller (SessionAuction) guarantees each
    ///      (lotId, seq) reaches here at most once, so summing never double-counts. Returns the running
    ///      session claim total.
    function recordClaim(bytes32 sessionId, address victim, uint128 provenHarm)
        external
        onlyAuction
        returns (uint256 totalClaims)
    {
        if (sessionId != ISessionBondConfig(msg.sender).sessionId()) revert ISessionAuction.Unauthorized(); // caller's own session (live read)
        if (sessionClosed[sessionId]) revert SessionAlreadyClosed(); // ledger sealed once closed

        Pool storage p = _pools[sessionId];
        if (p.settled) revert NothingToSettle(); // no late harm after the pool is distributed

        p.totalClaims += uint256(provenHarm);
        _harmOf[sessionId][victim] += provenHarm; // uint128 checked add

        emit ClaimRecorded(sessionId, victim, provenHarm, p.totalClaims);
        return p.totalClaims;
    }

    /// @inheritdoc IOperatorBond
    /// @dev onlyAuction; caller must be the clone for this session. The non-liveness slash: flags the
    ///      session so settleSlash can run with no victim claims; the whole pool then flows to Treasury as
    ///      the protocol-level liveness penalty (no specific victim).
    function slashNonLiveness(bytes32 sessionId, uint256 lotId) external onlyAuction {
        if (sessionId != ISessionBondConfig(msg.sender).sessionId()) revert ISessionAuction.Unauthorized();
        if (sessionClosed[sessionId]) revert SessionAlreadyClosed(); // ledger sealed once closed

        Pool storage p = _pools[sessionId];
        if (p.settled) revert NothingToSettle(); // cannot flag after the pool is distributed

        p.nonLiveness = true;
        emit NonLivenessSlashed(sessionId, lotId, p.bond);
    }

    /// @inheritdoc IOperatorBond
    /// @dev Permissionless once the session is closed. Distributes the whole session bond pool: toVictims
    ///      (= min(pool, totalClaims), claimable pro-rata via claimSlash) is set aside, the remainder goes
    ///      to Treasury, and p.bond is zeroed so the slashed stake is unwithdrawable. Reverts NothingToSettle
    ///      if nothing was recorded or it already settled. CEI: pool finalized before the Treasury push.
    function settleSlash(bytes32 sessionId) external nonReentrant {
        Pool storage p = _pools[sessionId];

        if (!sessionClosed[sessionId]) revert SessionNotClosed(); // cannot settle before all disputes can land
        if (p.settled || (p.totalClaims == 0 && !p.nonLiveness)) revert NothingToSettle();

        uint256 pool = p.bond;
        uint256 toVictims = pool >= p.totalClaims ? p.totalClaims : pool; // victims capped by the pool
        uint256 toTreasury = pool - toVictims;                            // remainder (incl. non-liveness)

        if (toTreasury != 0 && treasury == address(0)) revert ISessionAuction.ZeroAddress(); // never burn the remainder to a zero sink

        // EFFECTS first (CEI): snapshot the victim pot + divisor, zero the pool, settle.
        p.victimsPot = toVictims;
        p.settledClaims = p.totalClaims;
        p.bond = 0;
        p.settled = true;

        emit SlashSettled(sessionId, toVictims, toTreasury);
        if (toTreasury != 0) _pay(sessionToken[sessionId], treasury, toTreasury); // INTERACTION: remainder to Treasury (session's rail)
    }

    /// @notice Pull a victim's pro-rata slash share after settleSlash. Share is
    ///         victimsPot * recordedHarm / settledClaims; idempotent (harm zeroed on claim).
    function claimSlash(bytes32 sessionId) external nonReentrant {
        Pool storage p = _pools[sessionId];
        uint128 harm = _harmOf[sessionId][msg.sender];

        if (!p.settled || harm == 0 || p.settledClaims == 0) revert NothingToClaim();

        _harmOf[sessionId][msg.sender] = 0; // EFFECTS before payout (CEI)

        uint256 share = (p.victimsPot * uint256(harm)) / p.settledClaims;

        // Cap this session's running payout at its own snapshotted victimsPot, so its payouts cannot draw
        // down another session's stake from the shared singleton balance. Floor division strands at most
        // a few wei of victimsPot, the safe rounding direction (never an over-pay). No sweep of the
        // remainder: there is no on-chain "all victims claimed" signal, so a sweep could take an unclaimed
        // victim's share.
        uint256 remaining = p.victimsPot - claimedFromPot[sessionId];
        if (share > remaining) share = remaining;
        claimedFromPot[sessionId] += share;

        emit SlashClaimed(sessionId, msg.sender, share);
        if (share != 0) _pay(sessionToken[sessionId], msg.sender, share);
    }

    /// @inheritdoc IOperatorBond
    /// @dev An operator pulls its own remaining stake. After a slash the pool is 0, so payout caps to 0 and
    ///      the slashed stake is unrecoverable; a clean session (no claims) reclaims in full.
    function withdraw(bytes32 sessionId) external nonReentrant {
        Pool storage p = _pools[sessionId];
        // No stake before the session is closed, so an operator cannot front-run a victim's claim and
        // drain its bond before harm can be recorded.
        if (!sessionClosed[sessionId]) revert SessionNotClosed();
        // After close, an unresolved (recorded but unsettled) claim/slash still gates the unlock.
        if ((p.totalClaims != 0 || p.nonLiveness) && !p.settled) revert WindowOpen();

        uint256 amount = _stakeOf[sessionId][msg.sender];
        if (amount == 0) revert NothingToWithdraw();

        _stakeOf[sessionId][msg.sender] = 0; // EFFECTS first (CEI)

        // Pay only what the (post-slash) pool can cover: a settled-with-slash session has p.bond == 0.
        uint256 payout = amount <= p.bond ? amount : p.bond;
        p.bond -= payout;
        if (payout == 0) revert NothingToWithdraw(); // whole stake was slashed

        emit BondWithdrawn(sessionId, msg.sender, payout);
        _pay(sessionToken[sessionId], msg.sender, payout); // INTERACTION (session's rail)
    }

    /// @inheritdoc IOperatorBond
    function bondOf(bytes32 sessionId) external view returns (uint256) {
        return _pools[sessionId].bond;
    }

    /// @dev Token-aware gas-capped push with a per-token pendingWithdrawals credit fallback, so a hostile
    ///      recipient cannot DoS a slash or withdraw. Native (token==0) uses a 50k-gas call, an ERC-20 uses
    ///      trySafeTransfer; either failure credits the pull slot instead of reverting.
    function _pay(address token, address to, uint256 amount) private {
        if (amount == 0) return;

        bool ok;

        if (token == address(0)) {
            (ok,) = payable(to).call{value: amount, gas: 50_000}("");
        } else {
            ok = IERC20(token).trySafeTransfer(to, amount);
        }

        if (!ok) {
            pendingWithdrawals[token][to] += amount;
            emit WithdrawalCredited(token, to, amount);
        }
    }

    /// @notice Drain a failed-push credit to the caller (the pull half of the pull-over-push), per rail.
    function claimPending(address token) external nonReentrant {
        uint256 amount = pendingWithdrawals[token][msg.sender];
        if (amount == 0) revert NothingToWithdraw();

        pendingWithdrawals[token][msg.sender] = 0; // EFFECTS before payout (CEI)

        if (token == address(0)) {
            (bool ok,) = payable(msg.sender).call{value: amount}(""); // user-initiated: full gas, revert on fail
            if (!ok) revert NothingToWithdraw();
        } else {
            IERC20(token).safeTransfer(msg.sender, amount); // user-initiated: reverts on failure
        }

        emit WithdrawalClaimed(token, msg.sender, amount);
    }

    /// @dev Accept the Treasury-remainder return path and native funding.
    receive() external payable {}
}
