// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

// FlagRegistry: per-session merkle tree of "boundary leaves" over the sorted set of flagged paddles.
// The owner commits one root per session. Both membership and non-membership of a paddle are answered
// by a positive inclusion proof against that root, so neither can be faked by omitting a sibling.
//
// The leaf for an adjacent pair of the sorted flagged set (augmented with sentinels 0 and a max value)
// is keccak256(abi.encodePacked(uint16 low, uint16 high)). A proof carries the bracket endpoints
// (low, high) as its first two words; the verifier rebuilds the leaf from them and runs
// MerkleProof.verifyCalldata over the remaining siblings against the per-session root:
//   - membership of p:     a leaf with low == p (p is a flagged boundary low).
//   - non-membership of p: a leaf with low < p < high. Every flagged paddle is itself a low, so it can
//                          never sit strictly inside a bracket; such a proof exists iff p is unflagged.
// A bogus or too-short proof rebuilds the wrong hash (or fails the length/bracket guard) and returns
// false.

import {IFlagRegistry} from "./interfaces/IFlagRegistry.sol";
import {Ownable}       from "@openzeppelin/contracts/access/Ownable.sol";
import {MerkleProof}   from "@openzeppelin/contracts/utils/cryptography/MerkleProof.sol";

contract FlagRegistry is IFlagRegistry, Ownable {
    /// @dev Per-session committed root of the boundary-leaf flag tree. Zero means no flags for that
    ///      session, so verifyMembership is always false there.
    mapping(bytes32 sessionId => bytes32 root) private _root;

    event FlagRootCommitted(bytes32 indexed sessionId, bytes32 root);

    /// @notice Ownership (the ring-detection authority) starts at the deployer.
    constructor() Ownable(msg.sender) {}

    /// @notice Commit the per-session flag-tree root. Only the root lives on-chain; the tree is built
    ///         off-chain.
    function commitFlagRoot(bytes32 sessionId, bytes32 root) external onlyOwner {
        _root[sessionId] = root;
        emit FlagRootCommitted(sessionId, root);
    }

    /// @inheritdoc IFlagRegistry
    function rootOf(bytes32 sessionId) external view returns (bytes32) {
        return _root[sessionId];
    }

    /// @inheritdoc IFlagRegistry
    function verifyMembership(bytes32 sessionId, uint16 paddleId, bytes32[] calldata proof)
        external
        view
        returns (bool)
    {
        if (proof.length < 2) return false; // need at least the (low, high) bracket

        uint256 low = uint256(proof[0]);
        uint256 high = uint256(proof[1]);

        if (low >> 16 != 0 || high >> 16 != 0) return false; // low/high must fit uint16 (no dirty high bits)
        if (low != paddleId) return false; // membership: the flagged paddle is the leaf's low endpoint

        bytes32 leaf = keccak256(abi.encodePacked(uint16(low), uint16(high)));

        return MerkleProof.verifyCalldata(proof[2:], _root[sessionId], leaf);
    }

    /// @inheritdoc IFlagRegistry
    function verifyNonMembership(bytes32 sessionId, uint16 paddleId, bytes32[] calldata proof)
        external
        view
        returns (bool)
    {
        if (proof.length < 2) return false;

        uint256 low = uint256(proof[0]);
        uint256 high = uint256(proof[1]);

        // low/high must fit uint16: an inflated bracket (e.g. high = 65536 + realHigh) would pass the
        // paddleId < high check while the leaf hashes uint16(high) == realHigh, forging non-membership.
        if (low >> 16 != 0 || high >> 16 != 0) return false;

        // non-membership: the paddle is strictly bracketed by an in-tree boundary leaf (low < p < high).
        if (!(low < paddleId && paddleId < high)) return false;

        bytes32 leaf = keccak256(abi.encodePacked(uint16(low), uint16(high)));

        return MerkleProof.verifyCalldata(proof[2:], _root[sessionId], leaf);
    }
}
