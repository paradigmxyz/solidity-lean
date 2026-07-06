// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract CustomErrorHarnessTarget {
    error TooBig(uint256 value, uint256 limit);
    error PairBad(uint256 first, uint256 second);

    function check(uint256 value) external pure returns (uint256) {
        if (value > 10) {
            revert TooBig(value, 10);
        }

        return value + 1;
    }

    function named(uint256 value) external pure {
        revert PairBad({second: value + 2, first: value});
    }
}
