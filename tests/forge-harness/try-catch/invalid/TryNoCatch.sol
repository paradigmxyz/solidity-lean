// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface TryNoCatchTarget {
    function get() external returns (uint256);
}

contract TryNoCatch {
    function bad(TryNoCatchTarget target) external returns (uint256) {
        try target.get() {
            return 1;
        }
    }
}
