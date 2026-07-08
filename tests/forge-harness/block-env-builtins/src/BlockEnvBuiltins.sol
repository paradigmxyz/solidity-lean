// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Harness for the BLOCKHASH (blockhash(uint)) and BLOBHASH (blobhash(uint),
// EIP-4844) opcodes. blockhash returns a nonzero hash only for the most recent
// 256 blocks (block.number-256 ..= block.number-1); the current block, future
// blocks, and blocks older than 256 return 0. blobhash returns 0 for every
// index in a non-blob transaction (Foundry's default).
contract BlockEnvBuiltinsHarnessTarget {
    function blockHashOf(uint256 n) external view returns (bytes32) {
        return blockhash(n);
    }

    function blobHashOf(uint256 i) external view returns (bytes32) {
        return blobhash(i);
    }
}
