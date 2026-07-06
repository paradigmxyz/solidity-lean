// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ViewCreateTarget {}

contract ViewCreatesContract {
    function viewCreates() external view returns (uint256) {
        new ViewCreateTarget();
        return 1;
    }
}
