// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract PackedTruth {
    function test_packU8() public pure {
        require(keccak256(abi.encodePacked(uint8(0x12), uint8(0x34))) == keccak256(hex"1234"), "u8");
    }
    function test_packMixedWidth() public pure {
        require(keccak256(abi.encodePacked(uint16(0x1234), uint24(0x56789a))) == keccak256(hex"123456789a"), "mix");
    }
    function test_packNegI8() public pure {
        require(keccak256(abi.encodePacked(int8(-1))) == keccak256(hex"ff"), "i8");
    }
    function test_packU32() public pure {
        require(keccak256(abi.encodePacked(uint32(0x789abcde))) == keccak256(hex"789abcde"), "u32");
    }
    function test_packBool() public pure {
        require(keccak256(abi.encodePacked(true, false, uint8(7))) == keccak256(hex"010007"), "bool");
    }
}
