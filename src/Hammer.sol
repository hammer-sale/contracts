// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// Hammer is the factory singleton. It owns the SessionAuction implementation and clones one auction
// per session. createSession deploys a deterministic EIP-1167 clone, initializes it in the same tx
// (so no one can front-run initialize on the predicted address), and registers it on the Treasury and
// OperatorBond clone sets so their onlyAuction gates admit it. predictSession exposes the same
// deterministic address clients sign envelopes against.
//
// Access control is OZ Ownable; the deterministic-clone primitive is OZ Clones. Follows
// checks-effects-interactions: the clone deploy, initialize, and registerClone calls run only after
// all local checks and state writes.

import {Ownable} from "@openzeppelin/contracts/access/Ownable.sol";
import {Clones}  from "@openzeppelin/contracts/proxy/Clones.sol";

import {IHammer}         from "./interfaces/IHammer.sol";
import {ISessionAuction} from "./interfaces/ISessionAuction.sol";
import {ITreasury}       from "./interfaces/ITreasury.sol";
import {IOperatorBond}   from "./interfaces/IAgentBond.sol";
import {InitConfig}      from "./types/HammerTypes.sol";

/// @title Hammer
/// @notice Factory singleton that owns the SessionAuction implementation and clones one auction per
///         session. Only the owner (OZ `Ownable`) may deploy sessions.
contract Hammer is IHammer, Ownable {
    /// @notice The SessionAuction implementation cloned per session.
    address internal immutable _implementation;

    /// @notice Clone deployed for a sessionId (address(0) until createSession runs); enforces that a
    ///         sessionId is cloned at most once.
    mapping(bytes32 sessionId => address clone) internal _sessions;

    /// @notice House-vetted ERC-20 payment tokens. createSession rejects any ERC-20 not listed here, so a
    ///         fee-on-transfer / rebasing token cannot back a session escrow. Native ETH is always allowed.
    mapping(address token => bool allowed) internal _allowedPaymentToken;

    /// @notice Emitted once per deployed session clone (provenance for off-chain indexers).
    event SessionCreated(bytes32 indexed sessionId, address indexed clone);
    /// @notice Emitted when the owner allows / disallows an ERC-20 payment token for new sessions.
    event PaymentTokenAllowed(address indexed token, bool allowed);

    /// @notice The implementation address must carry code: an EIP-1167 clone of a codeless address
    ///         cannot be initialized and could be hijacked.
    error ImplementationHasNoCode();
    /// @notice A clone already exists for this sessionId; its deterministic salt would collide.
    error SessionExists();
    /// @notice The ERC-20 paymentToken is not on the house allowlist.
    error PaymentTokenNotAllowed(address token);

    /// @param implementation_ the SessionAuction implementation to clone (must already be deployed).
    constructor(address implementation_) Ownable(msg.sender) {
        if (implementation_.code.length == 0) revert ImplementationHasNoCode();

        _implementation = implementation_;
    }

    /// @inheritdoc IHammer
    function implementation() external view returns (address) {
        return _implementation;
    }

    /// @inheritdoc IHammer
    /// @dev Deterministic clone address for a sessionId: salt == keccak256(abi.encode(sessionId)),
    ///      deployer == this factory. Pure address derivation, no state read.
    function predictSession(bytes32 sessionId) external view returns (address) {
        return Clones.predictDeterministicAddress(
            _implementation,
            keccak256(abi.encode(sessionId)),
            address(this)
        );
    }

    /// @inheritdoc IHammer
    /// @dev cloneDeterministic, initialize in the same tx (so no one can front-run initialize on the
    ///      predicted address), then registerClone on Treasury + OperatorBond so their onlyAuction
    ///      gates admit the clone.
    function createSession(InitConfig calldata cfg) external onlyOwner returns (address clone) {
        bytes32 sessionId = cfg.sessionId;

        // Guards: a sessionId is cloned at most once, and ERC-20 payment tokens must be allowlisted
        // (native ETH is exempt).
        if (_sessions[sessionId] != address(0)) revert SessionExists();
        if (cfg.paymentToken != address(0) && !_allowedPaymentToken[cfg.paymentToken]) {
            revert PaymentTokenNotAllowed(cfg.paymentToken);
        }

        // Salt is derived from the sessionId so the deploy lands on the predicted address.
        // cloneDeterministic also reverts on salt collision, backstopping the SessionExists guard.
        clone = Clones.cloneDeterministic(_implementation, keccak256(abi.encode(sessionId)));

        // Record the clone before the external initialize / registerClone calls (checks-effects-interactions).
        _sessions[sessionId] = clone;
        emit SessionCreated(sessionId, clone);

        // Initialize the clone, then register it so the Treasury and OperatorBond onlyAuction gates
        // (which admit only registered clones) accept calls from it.
        ISessionAuction(clone).initialize(cfg);
        ITreasury(cfg.treasury).registerClone(clone);
        IOperatorBond(cfg.operatorBond).registerClone(clone);
    }

    /// @notice Allow / disallow an ERC-20 as a session payment token. Reverts on address(0): native ETH is
    ///         always permitted and is never listed.
    function setPaymentTokenAllowed(address token, bool allowed) external onlyOwner {
        if (token == address(0)) revert PaymentTokenNotAllowed(token);

        _allowedPaymentToken[token] = allowed;
        emit PaymentTokenAllowed(token, allowed);
    }

    /// @notice True if `token` may back a new session escrow: native ETH always, ERC-20 only if allowlisted.
    function isPaymentTokenAllowed(address token) external view returns (bool) {
        return token == address(0) || _allowedPaymentToken[token];
    }
}
