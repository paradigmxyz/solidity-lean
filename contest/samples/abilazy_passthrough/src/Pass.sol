// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract Pass {
    // Bare parameter passthrough: no arithmetic that would force an ABI cleanup.
    function f(uint8 x) external pure returns (uint8) {
        return x;
    }
}
