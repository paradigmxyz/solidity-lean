// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Packed {
    // solc: 12 34 (2 bytes, narrow uint8 no padding)
    function packU8() external pure returns (bytes memory) {
        return abi.encodePacked(uint8(0x12), uint8(0x34));
    }

    // solc: 1234 56789a (uint16 then uint24) = 12 34 56 78 9a (5 bytes)
    function packMixedWidth() external pure returns (bytes memory) {
        return abi.encodePacked(uint16(0x1234), uint24(0x56789a));
    }

    // solc: ff (int8 -1 = 1 byte 0xff)
    function packNegI8() external pure returns (bytes memory) {
        return abi.encodePacked(int8(-1));
    }

    // solc: aabbccdd ff (bytes4 then bytes1) = 5 bytes
    function packBytesN() external pure returns (bytes memory) {
        return abi.encodePacked(bytes4(0xaabbccdd), bytes1(0xff));
    }

    // solc: 01 00 07 (bool true/false + uint8)
    function packBool() external pure returns (bytes memory) {
        return abi.encodePacked(true, false, uint8(7));
    }

    // solc: 41424344 (string concat "AB"+"CD")
    function packStr() external pure returns (bytes memory) {
        return abi.encodePacked("AB", "CD");
    }

    // solc: array uint8[3] each padded to 32 bytes => 96 bytes
    function packU8Array() external pure returns (bytes memory) {
        uint8[3] memory a = [uint8(1), 2, 3];
        return abi.encodePacked(a);
    }

    // abi.encode of uint8,uint16 -> 2 words padded
    function encU8U16() external pure returns (bytes memory) {
        return abi.encode(uint8(0x12), uint16(0x3456));
    }

    // uint32 full-width packed = 4 bytes
    function packU32() external pure returns (bytes memory) {
        return abi.encodePacked(uint32(0x789abcde));
    }
}
