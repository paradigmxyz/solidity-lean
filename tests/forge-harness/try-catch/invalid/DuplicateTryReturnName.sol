// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

interface DuplicateTryReturnNameTarget {
    function pair() external returns (uint256, uint256);
}

contract DuplicateTryReturnName {
    function bad(DuplicateTryReturnNameTarget target) external returns (uint256) {
        try target.pair() returns (uint256 value, uint256 value) {
            return value;
        } catch {
            return 0;
        }
    }
}
