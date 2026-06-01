// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Treasury: forfeit pool shared by every session clone. It holds only forfeited offender escrow routed
// in via depositForfeit (never bidder principal) and splits it through a waterfall whose residual lands
// in a sink no colluding party controls.
//
// Config comes from two places:
//   - paymentToken, feeRecipient, arbiter: per-session, read off the calling clone and snapshotted into
//     the forfeit record at depositForfeit, then never re-read.
//   - forfeitChallengeSec, counterBondBps, disruptionRebateBps, disruptionRebateCap, houseFeeBps,
//     neutralSink: owner-tunable Treasury-side governance config.
//
// onlyAuction checks the factory-registered clone set (see registerClone), not a single stored address,
// so all clones share this one Treasury.

import {ITreasury}      from "./interfaces/ITreasury.sol";
import {ISessionAuction} from "./interfaces/ISessionAuction.sol";
import {Ownable}        from "@openzeppelin/contracts/access/Ownable.sol";
import {SafeERC20}      from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import {IERC20}         from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {ReentrancyGuardTransient} from "@openzeppelin/contracts/utils/ReentrancyGuardTransient.sol";

/// @dev Read surface the Treasury snapshots from the registered clone at depositForfeit: the rail the
///      forfeit is denominated in, the house fee recipient, and the arbiter that rules the dispute.
interface ISessionForfeitConfig {
    function paymentToken() external view returns (address);
    function feeRecipient() external view returns (address);
    function arbiter() external view returns (address);
}

contract Treasury is ITreasury, Ownable, ReentrancyGuardTransient {
    using SafeERC20 for IERC20;

    // Owner-tunable governance config, shown with defaults: 1-hour contest window, 10% counter-bond,
    // 1% rebate capped at 10 ether, 20%-of-remainder house cut.
    uint32  public forfeitChallengeSec   = 1 hours;
    uint16  public counterBondBps        = 1_000;    // 10% of stored forfeitAmount
    uint16  public disruptionRebateBps   = 100;      // 1% of remainder
    uint128 public disruptionRebateCap   = 10 ether; // bounds the rebate so a false flag has limited payoff
    uint16  public houseFeeBps           = 2_000;    // 20% of remainder

    /// @dev Burn address no colluding party controls; the waterfall residual (`rest`) leaves here so the
    ///      whole forfeit is disbursed and no reachable party absorbs the bulk. Must be non-zero because
    ///      the OZ ERC-20 rail rejects transfers to address(0).
    address public neutralSink = address(0x000000000000000000000000000000000000dEaD);

    /// @dev Factory-registered clone set the onlyAuction gate checks.
    mapping(address clone => bool) public isRegisteredClone;

    /// @dev Per-(token, account) credit for a recipient that rejected a push, drained via claimPending,
    ///      so one reverting payee cannot strand the waterfall (pull-over-push). Keyed by token because
    ///      Treasury holds forfeits across multiple session rails.
    mapping(address token => mapping(address account => uint256 amount)) public pendingWithdrawals;

    struct Forfeit {
        address offender;         // flagged loser; the only party that may challenge
        address promotedWinner;   // promoted underbidder; receives the capped disruption rebate
        address seller;           // made whole first for the clearing-vs-promoted gap
        address feeRecipient;     // session-configured house fee recipient (snapshotted)
        address arbiter;          // session-configured arbiter (snapshotted); rules resolveChallenge
        address paymentToken;     // rail this forfeit is denominated in; address(0) == native ETH
        uint256 forfeitAmount;    // snapshotted offender escrow; the basis the waterfall splits
        uint256 offenderClearing; // offender's clearing price; feeds the seller make-whole gap only
        uint256 promotedPrice;    // promoted winner's own bid (the lower clearing the make-whole closes)
        uint256 counterBond;      // offender's posted counter-bond; 0 until challenged
        uint64  depositedAt;      // window anchor: disburse callable after depositedAt + forfeitChallengeSec
        bool    challenged;       // set by challenge(); blocks disburse until the arbiter rules
        bool    resolved;         // terminal: set once disbursed or the challenge is resolved
    }

    mapping(bytes32 forfeitId => Forfeit) public forfeits;

    event ForfeitDeposited(
        bytes32 indexed forfeitId,
        address indexed offender,
        address indexed promotedWinner,
        uint256 lotId,
        uint256 forfeitAmount,
        address paymentToken
    );
    event ForfeitChallenged(bytes32 indexed forfeitId, address indexed offender, uint256 counterBond);
    event ForfeitChallengeResolved(bytes32 indexed forfeitId, bool offenderWasInnocent);
    event ForfeitDisbursed(
        bytes32 indexed forfeitId,
        uint256 sellerMakeWhole,
        uint256 rebate,
        uint256 house,
        uint256 sink
    );
    event CloneRegistered(address indexed clone);
    event WithdrawalCredited(address indexed account, address indexed token, uint256 amount); // on a rejected push
    event WithdrawalClaimed(address indexed account, address indexed token, uint256 amount);

    /// @dev Caller must be in the factory-registered clone set. Reverts with ISessionAuction.Unauthorized,
    ///      reused because the Treasury surface declares no errors of its own.
    modifier onlyAuction() {
        if (!isRegisteredClone[msg.sender]) revert ISessionAuction.Unauthorized();
        _;
    }

    // Owner (registrar) starts at the deployer, transferable via OZ Ownable.
    constructor() Ownable(msg.sender) {}

    /// @notice Hammer factory, authorized alongside the owner so it can register a clone in the same tx
    ///         that creates the session. Set post-deploy, since the factory is deployed after Treasury.
    address public factory;

    function setFactory(address f) external onlyOwner {
        factory = f;
    }

    /// @dev Registers a clone so onlyAuction passes for it. Admits the owner (registrar) or the factory
    ///      (in-tx session-creation path); any other caller is rejected, otherwise a contract could
    ///      self-register and defeat the onlyAuction gate.
    function registerClone(address clone) external {
        if (msg.sender != owner() && msg.sender != factory) revert ISessionAuction.Unauthorized();
        isRegisteredClone[clone] = true;
        emit CloneRegistered(clone);
    }

    /// @notice Clone routes an offender's forfeited escrow here on the session rail. Native asserts
    ///         msg.value == forfeitAmount (strict); ERC-20 pulls forfeitAmount via safeTransferFrom and
    ///         asserts msg.value == 0. forfeitAmount is the basis both disburse and challenge work from.
    function depositForfeit(
        address offender,
        address promotedWinner,
        uint256 lotId,
        uint256 forfeitAmount,
        uint256 offenderClearing,
        uint256 promotedPrice,
        address seller
    ) external payable onlyAuction returns (bytes32 forfeitId) {
        // id keyed on (clone, offender, lotId): one forfeit per void on a given clone/lot.
        forfeitId = keccak256(abi.encode(msg.sender, offender, lotId));

        // Reject a zero amount (the re-deposit guard relies on forfeitAmount != 0 marking a live record)
        // and a re-deposit onto an existing id.
        if (forfeitAmount == 0) revert ISessionAuction.NoEscrow();
        if (forfeits[forfeitId].forfeitAmount != 0) revert ISessionAuction.EscrowAlreadyReleased();

        // Snapshot the session rail + payout addresses from the calling clone.
        address token = ISessionForfeitConfig(msg.sender).paymentToken();
        address feeRecipient_ = ISessionForfeitConfig(msg.sender).feeRecipient();
        address arbiter_ = ISessionForfeitConfig(msg.sender).arbiter();

        // Fund the forfeit on its rail. Strict equality on the native rail (never >=) rejects an under-
        // or over-paying clone so no surplus wei leaks into the accounting; the token rail pulls exactly
        // forfeitAmount (the clone pre-approves Treasury) and allows no native value.
        if (token == address(0)) {
            if (msg.value != forfeitAmount) revert ISessionAuction.WrongDenomination();
        } else {
            if (msg.value != 0) revert ISessionAuction.WrongDenomination();
            IERC20(token).safeTransferFrom(msg.sender, address(this), forfeitAmount);
        }

        forfeits[forfeitId] = Forfeit({
            offender: offender,
            promotedWinner: promotedWinner,
            seller: seller,
            feeRecipient: feeRecipient_,
            arbiter: arbiter_,
            paymentToken: token,
            forfeitAmount: forfeitAmount,
            offenderClearing: offenderClearing,
            promotedPrice: promotedPrice,
            counterBond: 0,
            depositedAt: uint64(block.timestamp),
            challenged: false,
            resolved: false
        });

        emit ForfeitDeposited(forfeitId, offender, promotedWinner, lotId, forfeitAmount, token);
    }

    /// @notice Offender contests the void with a counter-bond >= forfeitAmount * counterBondBps / 1e4,
    ///         setting challenged = true so disburse is blocked until the arbiter rules. Bond follows the
    ///         session rail (native msg.value, else a token pull).
    function challenge(bytes32 forfeitId) external payable nonReentrant {
        Forfeit storage f = forfeits[forfeitId];

        // Only the recorded offender may challenge (a non-existent forfeit's offender is address(0)).
        // Reject a resolved forfeit, since an innocent ruling after disburse would pay forfeitAmount a
        // second time out of the shared pool. The window must still be open: once it elapses disburse
        // owns the forfeit, so challenge and disburse are never simultaneously live.
        if (msg.sender != f.offender) revert ISessionAuction.Unauthorized();
        if (f.resolved) revert ISessionAuction.EscrowAlreadyReleased();
        if (f.challenged) revert ISessionAuction.AlreadyDisputed();
        if (block.timestamp >= uint256(f.depositedAt) + forfeitChallengeSec) revert ISessionAuction.AcWindowClosed();

        uint256 minBond = (f.forfeitAmount * counterBondBps) / 1e4;

        // Bond follows the forfeit's rail: native takes msg.value (must be >= minBond); the token rail
        // carries no native value and pulls exactly minBond from the offender.
        uint256 bond;
        if (f.paymentToken == address(0)) {
            bond = msg.value;
            if (bond < minBond) revert ISessionAuction.WrongBond();
        } else {
            if (msg.value != 0) revert ISessionAuction.WrongDenomination();
            bond = minBond;
            IERC20(f.paymentToken).safeTransferFrom(msg.sender, address(this), bond);
        }

        f.counterBond = bond;
        f.challenged = true;

        emit ForfeitChallenged(forfeitId, msg.sender, bond);
    }

    /// @notice Recorded arbiter rules an open challenge. offenderWasInnocent == true returns escrow +
    ///         counter-bond to the offender and runs no waterfall (the void is unwound only at the
    ///         Treasury layer). offenderWasInnocent == false forfeits the bond to the neutral sink and
    ///         runs the waterfall over forfeitAmount.
    function resolveChallenge(bytes32 forfeitId, bool offenderWasInnocent) external nonReentrant {
        Forfeit storage f = forfeits[forfeitId];

        // Only the recorded arbiter (a non-existent forfeit's arbiter is address(0)), only on an open
        // challenge, and only once.
        if (msg.sender != f.arbiter) revert ISessionAuction.Unauthorized();
        if (!f.challenged) revert ISessionAuction.AlreadyDisputed();
        if (f.resolved) revert ISessionAuction.EscrowAlreadyReleased();

        // Mark terminal before any external value move so a reentrant call sees the resolved forfeit.
        f.resolved = true;

        emit ForfeitChallengeResolved(forfeitId, offenderWasInnocent);

        if (offenderWasInnocent) {
            // Flag overturned: return escrow + counter-bond, no waterfall.
            _pay(f.paymentToken, f.offender, f.forfeitAmount + f.counterBond);
        } else {
            // Flag upheld: counter-bond forfeited to the neutral sink, then the waterfall runs.
            if (f.counterBond != 0) _pay(f.paymentToken, neutralSink, f.counterBond);
            _runWaterfall(forfeitId, f);
        }
    }

    /// @notice Permissionless once the contest window closes and the forfeit is unchallenged; runs the
    ///         waterfall over forfeitAmount. Reverts if the window is still open, if challenged (the
    ///         arbiter must rule first), or if there is nothing to disburse.
    function disburse(bytes32 forfeitId) external nonReentrant {
        Forfeit storage f = forfeits[forfeitId];

        // Permissionless, so the guards reject by forfeit state, not by caller: already resolved, a
        // non-existent forfeit (forfeitAmount == 0), still challenged (the arbiter must rule first), or
        // the contest window still open.
        if (f.resolved) revert ISessionAuction.NothingToWithdraw();
        if (f.forfeitAmount == 0) revert ISessionAuction.NoEscrow();
        if (f.challenged) revert ISessionAuction.AlreadyDisputed();
        if (block.timestamp < uint256(f.depositedAt) + forfeitChallengeSec) revert ISessionAuction.AcWindowOpen();

        // Mark terminal before the splits leave so a reentrant call sees the resolved forfeit.
        f.resolved = true;

        _runWaterfall(forfeitId, f);
    }

    /// @dev Splits forfeitAmount in order: seller make-whole for the clearing-vs-promoted gap, then a
    ///      capped disruption rebate to the promoted winner, then the house cut to feeRecipient, then the
    ///      rest to the neutral sink. The four components sum to forfeitAmount, so the entire forfeit
    ///      leaves Treasury and the residual lands somewhere no colluding party controls.
    function _runWaterfall(bytes32 forfeitId, Forfeit storage f) private {
        uint256 amount = f.forfeitAmount;

        // 1. sellerMakeWhole = min(forfeitAmount, offenderClearing - promotedPrice) -> seller.
        uint256 gap = f.offenderClearing > f.promotedPrice ? f.offenderClearing - f.promotedPrice : 0;
        uint256 sellerMakeWhole = gap < amount ? gap : amount;

        // 2. remainder.
        uint256 remainder = amount - sellerMakeWhole;

        // 3. rebate = min(remainder * disruptionRebateBps / 1e4, disruptionRebateCap) -> promotedWinner.
        uint256 rebate = (remainder * disruptionRebateBps) / 1e4;
        if (rebate > disruptionRebateCap) rebate = disruptionRebateCap;

        // 4. house = remainder * houseFeeBps / 1e4 -> feeRecipient. Clamp to the post-rebate balance so
        //    even a misconfigured bps + cap can never underflow `rest` and brick disburse.
        uint256 house = (remainder * houseFeeBps) / 1e4;
        if (house > remainder - rebate) house = remainder - rebate;

        // 5. rest -> neutralSink (conserved residual). No underflow: rebate <= remainder and house is
        //    clamped above.
        uint256 rest = remainder - rebate - house;

        // Pay out on the forfeit's rail in waterfall order: seller, rebate, house, residual.
        _pay(f.paymentToken, f.seller, sellerMakeWhole);
        _pay(f.paymentToken, f.promotedWinner, rebate);
        _pay(f.paymentToken, f.feeRecipient, house);
        _pay(f.paymentToken, neutralSink, rest);

        emit ForfeitDisbursed(forfeitId, sellerMakeWhole, rebate, house, rest);
    }

    /// @dev Rail-aware pay-out: native uses a bounded-gas call, ERC-20 uses trySafeTransfer. A rejected
    ///      push is credited to pendingWithdrawals (pull-over-push) instead of reverting, so one hostile
    ///      or contract recipient cannot brick the whole waterfall.
    function _pay(address token, address to, uint256 amount) private {
        if (amount == 0) return;

        if (token == address(0)) {
            (bool ok,) = payable(to).call{value: amount, gas: 50_000}("");
            if (!ok) {
                pendingWithdrawals[token][to] += amount;
                emit WithdrawalCredited(to, token, amount);
            }
        } else {
            if (!IERC20(token).trySafeTransfer(to, amount)) {
                pendingWithdrawals[token][to] += amount;
                emit WithdrawalCredited(to, token, amount);
            }
        }
    }

    /// @notice Drain the caller's failed-push credit for `token` (the pull half of pull-over-push).
    function claimPending(address token) external nonReentrant {
        uint256 amount = pendingWithdrawals[token][msg.sender];
        if (amount == 0) revert ISessionAuction.NothingToWithdraw();

        // Zero the credit before paying out so a reentrant claim sees nothing left.
        pendingWithdrawals[token][msg.sender] = 0;

        // User-initiated, so unlike the _pay push this uses full gas and reverts on failure rather than
        // re-crediting.
        if (token == address(0)) {
            (bool ok,) = payable(msg.sender).call{value: amount}("");
            if (!ok) revert ISessionAuction.NothingToWithdraw();
        } else {
            IERC20(token).safeTransfer(msg.sender, amount);
        }

        emit WithdrawalClaimed(msg.sender, token, amount);
    }

    /// @dev Accept native funding (the clone forwards the forfeit / counter-bond as msg.value).
    receive() external payable {}
}
