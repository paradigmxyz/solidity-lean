// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bytes2ToUint8 {
    function convert(bytes2 input) external pure returns (uint8) {
        return uint8(input);
    }
}
