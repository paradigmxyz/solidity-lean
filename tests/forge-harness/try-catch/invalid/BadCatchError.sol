// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface BadCatchErrorTarget {
    function fail() external;
}

contract BadCatchError {
    function bad(BadCatchErrorTarget target) external returns (uint256) {
        try target.fail() {
            return 1;
        } catch Error(uint256 code) {
            return code;
        }
    }
}
