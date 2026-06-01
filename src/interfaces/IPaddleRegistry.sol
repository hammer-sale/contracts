// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// @title IPaddleRegistry
/// @notice Maps a KYC-cleared principal to its bidding paddle number.
interface IPaddleRegistry {
    /// @notice Paddle assigned to a principal; 0 means unregistered, so placeBid reverts Unauthorized.
    /// @param principal Address to look up.
    /// @return Paddle number, or 0 if the principal has no paddle.
    function paddleOf(address principal) external view returns (uint16);
}
