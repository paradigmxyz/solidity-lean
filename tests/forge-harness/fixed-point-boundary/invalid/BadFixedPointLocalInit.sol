// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract BadFixedPointLocalInit {
    function run() external pure returns (uint256) {
        fixed128x18 value = 1.25;
        return 1;
    }
}
