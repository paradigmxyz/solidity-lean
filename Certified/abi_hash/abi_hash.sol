// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract AbiHash {
    function hashPair(uint256 a, uint256 b) external pure returns (uint256) {
        return uint256(keccak256(abi.encode(a, b)));
    }
}
