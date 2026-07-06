// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Uint32ToBytes2 {
    function convert(uint32 input) external pure returns (bytes2) {
        return bytes2(input);
    }
}
