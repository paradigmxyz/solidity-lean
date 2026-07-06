// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract BadFixedPointImplicit {
    function bad(ufixed8x1 input) external pure returns (fixed8x1) {
        return input;
    }
}
