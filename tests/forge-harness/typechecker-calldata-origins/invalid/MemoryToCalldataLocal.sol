// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryToCalldataLocal {
    function bad(uint256[] memory input) public pure returns (uint256) {
        uint256[] calldata local = input;
        return local.length;
    }
}
