// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract BadFixedPointLiteral {
    function run() external pure returns (fixed128x18) {
        return 1.25;
    }
}
