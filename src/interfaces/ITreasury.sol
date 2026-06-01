// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// @title ITreasury
/// @notice Escrows a defaulting winner's slashed funds and pays them out via a waterfall that
///         leaves the offender no gain. The forfeit amount is passed explicitly rather than read
///         from msg.value, so a single set of functions serves both the native and ERC20 rails
///         (the implementation branches on the session's paymentToken).
interface ITreasury {
    /// @notice Escrow a slashed forfeit. Restricted to auction clones registered via registerClone.
    /// @param forfeitAmount slashed value to escrow, in native wei or ERC20 units
    function depositForfeit(
        address offender, address promotedWinner, uint256 lotId,
        uint256 forfeitAmount,
        uint256 offenderClearing, uint256 promotedPrice, address seller
    ) external payable returns (bytes32 forfeitId);

    /// @notice Offender contests the forfeit. Requires a bond of forfeitAmount * counterBondBps / 1e4.
    function challenge(bytes32 forfeitId) external payable;

    /// @notice Arbiter rules on a challenge. offenderWasInnocent true refunds the offender.
    function resolveChallenge(bytes32 forfeitId, bool offenderWasInnocent) external;

    /// @notice Run the payout waterfall once a forfeit is past its window unchallenged.
    function disburse(bytes32 forfeitId) external;

    /// @notice Add an auction clone to the allowlist that may call depositForfeit. Called by the
    ///         factory at deploy time.
    function registerClone(address clone) external;
}
