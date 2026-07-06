// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Uint8ToInt16 {
    function convert(uint8 input) external pure returns (int16) {
        return int16(input);
    }
}
