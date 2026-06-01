// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {InitConfig} from "../types/HammerTypes.sol";

/// @title IHammer
/// @notice Factory singleton for the auction protocol. Clones the SessionAuction implementation
///         once per session and acts as the onlyHammer authority on every clone it creates.
interface IHammer {
    /// @notice The SessionAuction implementation cloned per session.
    function implementation() external view returns (address);

    /// @notice Address the clone for sessionId would deploy to.
    /// @dev Deterministic CREATE2 address; the salt is keccak256(abi.encode(sessionId)).
    function predictSession(bytes32 sessionId) external view returns (address);

    /// @notice Deploy and initialize a SessionAuction clone for the session, then register it on
    ///         the Treasury and OperatorBond so their auction-only gates admit it.
    /// @return clone The deployed clone address (matches predictSession for the same sessionId).
    function createSession(InitConfig calldata cfg) external returns (address clone);
}
