// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Int8ToUint16 {
    function convert(int8 input) external pure returns (uint16) {
        return uint16(input);
    }
}
