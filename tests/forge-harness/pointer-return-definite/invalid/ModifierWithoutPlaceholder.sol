// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ModifierWithoutPlaceholder {
    modifier bad() {
        uint256 value = 1;
        value;
    }

    function f() external bad returns (uint256) {
        return 1;
    }
}
