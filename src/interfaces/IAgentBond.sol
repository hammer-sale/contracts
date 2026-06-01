// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// @title IOperatorBond
/// @notice Per-session economic bond for the registered operator set. Each operator stakes per
///         session, harm claims accrue to a ledger, and on settlement the stake pays victims
///         pro-rata before the operator withdraws the remainder. This gives economic stake and
///         liveness containment only; bid blindness comes from the enclave, not from this bond.
/// @dev Concrete implementation is AgentBond.sol. The interface name differs from the file name.
interface IOperatorBond {
    // Stake on the session's rail, read from the (registered, session-owning) clone's paymentToken:
    // native if it is address(0) (msg.value == amount), else ERC-20 (msg.value == 0, amount pulled).
    function deposit(bytes32 sessionId, address clone, uint256 amount) external payable;

    // Caller must be the session's auction clone. Adds provenHarm to the victim's claim ledger and
    // returns the running total of claims against the session.
    function recordClaim(bytes32 sessionId, address victim, uint128 provenHarm) external returns (uint256 totalClaims);

    // Pays recorded victims pro-rata up to bidderShareBps of the stake; any remainder goes to Treasury.
    function settleSlash(bytes32 sessionId) external;

    // Caller must be the session's auction clone. Slashes the stake for a missed liveness deadline.
    function slashNonLiveness(bytes32 sessionId, uint256 lotId) external;

    // Permissionless, but reverts before the clone's bondClaimsCloseAt() and requires a registered
    // clone that owns sessionId. Seals the claim ledger and unlocks settleSlash and withdraw.
    function closeSession(bytes32 sessionId, address clone) external;

    // Returns the remaining bond to the staked operator. Allowed only after closeSession and with no
    // open dispute or claim.
    function withdraw(bytes32 sessionId) external;

    // Current bond balance staked for the session.
    function bondOf(bytes32 sessionId) external view returns (uint256);

    // The deploy path registers each session clone here so its calls pass the onlyAuction gate.
    function registerClone(address clone) external;
}
