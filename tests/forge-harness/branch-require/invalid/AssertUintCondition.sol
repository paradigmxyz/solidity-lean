// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract AssertUintCondition {
    function bad() external pure {
        assert(uint256(1));
    }
}
