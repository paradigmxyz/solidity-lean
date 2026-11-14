// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract AbiEncode {
    function hashPair(uint256 a, uint256 b) external pure returns (bytes32) {
        return keccak256(abi.encode(a, b));
    }
}
