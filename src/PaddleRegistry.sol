// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {IPaddleRegistry} from "./interfaces/IPaddleRegistry.sol";
import {Ownable} from "@openzeppelin/contracts/access/Ownable.sol";

/// @title PaddleRegistry
/// @notice KYC paddle registry: maps a verified principal to a 1-based `uint16` paddleId.
///         `paddleOf(p) == 0` means unregistered, which `SessionAuction.placeBid` treats as the
///         KYC gate (an unregistered principal cannot bid). Paddle 0 is permanently reserved as
///         the "unregistered" sentinel; ids are assigned sequentially starting at 1.
/// @dev    `paddleOf` is the only read other contracts depend on; the admin functions below are
///         owner-gated (OZ `Ownable`) to the house KYC operator. Ownership starts at the deployer
///         and is transferable.
contract PaddleRegistry is IPaddleRegistry, Ownable {
    /// @dev Next id to assign. Starts at 1; paddle 0 is the unregistered sentinel.
    uint16 private _nextPaddleId;

    mapping(address principal => uint16 paddleId) private _paddleOf;

    event PaddleRegistered(address indexed principal, uint16 indexed paddleId);
    event PaddleRevoked(address indexed principal, uint16 indexed paddleId);

    error AlreadyRegistered(address principal);
    error NotRegistered(address principal);
    error PaddleSpaceExhausted();

    constructor() Ownable(msg.sender) {
        _nextPaddleId = 1;
    }

    /// @inheritdoc IPaddleRegistry
    function paddleOf(address principal) external view returns (uint16) {
        return _paddleOf[principal];
    }

    /// @notice Assign the next sequential paddle to a KYC-verified principal.
    /// @dev Reverts `AlreadyRegistered` if the principal already holds a paddle, and
    ///      `PaddleSpaceExhausted` once the 1..65535 space is used up.
    function register(address principal) external onlyOwner returns (uint16 paddleId) {
        if (_paddleOf[principal] != 0) revert AlreadyRegistered(principal);

        paddleId = _nextPaddleId;

        // type(uint16).max is reserved: FlagRegistry uses it as its non-membership sentinel, so a
        // paddle of 65535 could never prove non-membership. Assign only 1..65534; the 0 check
        // catches a call after _nextPaddleId has wrapped past the ceiling.
        if (paddleId == 0 || paddleId == type(uint16).max) revert PaddleSpaceExhausted();

        _paddleOf[principal] = paddleId;

        // Wraps to 0 at the ceiling; the guard above rejects the next call, so no silent reuse.
        unchecked {
            _nextPaddleId = paddleId + 1;
        }

        emit PaddleRegistered(principal, paddleId);
    }

    /// @notice Revoke a principal's paddle (e.g. failed KYC re-check). `paddleOf` returns 0 after.
    /// @dev The id is retired, not recycled, so paddle history stays unambiguous.
    function revoke(address principal) external onlyOwner {
        uint16 paddleId = _paddleOf[principal];
        if (paddleId == 0) revert NotRegistered(principal);

        delete _paddleOf[principal];

        emit PaddleRevoked(principal, paddleId);
    }
}
