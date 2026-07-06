// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface TryReturnsNoCatchTarget {
    function get() external returns (uint256);
}

contract TryReturnsNoCatch {
    function bad(TryReturnsNoCatchTarget target) external returns (uint256) {
        try target.get() returns (uint256 value) {
            return value;
        }
    }
}
