// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract KeccakUint {
    function bad() external pure returns (bytes32) {
        return keccak256(uint256(1));
    }
}
