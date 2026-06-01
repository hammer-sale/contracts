// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// @title IFlagRegistry
/// @notice Per-session Merkle tree of sorted boundary leaves, one leaf per flagged paddle.
///         Each leaf is a (low, high) range whose low endpoint is the flagged paddleId.
///         Both membership and non-membership are proven by an inclusion proof that must
///         succeed, so a caller cannot fake either answer by simply withholding a proof.
interface IFlagRegistry {
    /// @notice Merkle root committing the flagged-paddle set for a session.
    /// @param sessionId Auction session.
    /// @return The committed root, or zero if no set has been committed.
    function rootOf(bytes32 sessionId) external view returns (bytes32);

    /// @notice True if paddleId is flagged: a leaf whose low endpoint equals paddleId is in the tree.
    /// @param sessionId Auction session.
    /// @param paddleId Paddle to test for membership.
    /// @param proof [bytes32(uint256(low)), bytes32(uint256(high)), siblings...]; fails unless low == paddleId.
    /// @return Whether paddleId is flagged.
    function verifyMembership(bytes32 sessionId, uint16 paddleId, bytes32[] calldata proof)
        external view returns (bool);

    /// @notice True if paddleId is not flagged: a leaf strictly brackets it (low < paddleId < high).
    ///         A flagged paddle equals some leaf's low endpoint, so it can never satisfy this.
    /// @param sessionId Auction session.
    /// @param paddleId Paddle to test for non-membership.
    /// @param proof Same layout as verifyMembership: [low, high, siblings...] as bytes32 words.
    /// @return Whether paddleId is absent from the flagged set.
    function verifyNonMembership(bytes32 sessionId, uint16 paddleId, bytes32[] calldata proof)
        external view returns (bool);
}
