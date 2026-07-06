// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract NumericBytesConversions {
    function uint16FromUint8(uint8 input) external pure returns (uint16) {
        return uint16(input);
    }

    function uint8FromUint16(uint16 input) external pure returns (uint8) {
        return uint8(input);
    }

    function uint8FromInt8(int8 input) external pure returns (uint8) {
        return uint8(input);
    }

    function int8FromUint8(uint8 input) external pure returns (int8) {
        return int8(input);
    }

    function bytes4FromBytes2(bytes2 input) external pure returns (bytes4) {
        return bytes4(input);
    }

    function bytes2FromBytes4(bytes4 input) external pure returns (bytes2) {
        return bytes2(input);
    }

    function bytes2FromUint16(uint16 input) external pure returns (bytes2) {
        return bytes2(input);
    }

    function uint16FromBytes2(bytes2 input) external pure returns (uint16) {
        return uint16(input);
    }
}
