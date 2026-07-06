// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ValueTypeMemoryParam {
    function bad(uint256 memory value) external pure returns (uint256) {
        return value;
    }
}
