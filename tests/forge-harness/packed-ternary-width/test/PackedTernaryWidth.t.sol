// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/PackedTernaryWidth.sol";

contract PackedTernaryWidthForgeTest {
    PackedTernaryWidth private target;

    function setUp() public {
        target = new PackedTernaryWidth();
    }

    function testThenBranchPacksCommonWidth() public view {
        // cond == true selects a == 0x11 (uint8), but the common type is uint16,
        // so it is packed as two bytes 0x0011, NOT the one byte 0x11.
        require(
            target.packedHash(true) == keccak256(hex"0011"),
            "then-branch common width"
        );
        require(
            target.packedHash(true) ==
                0xd5842eca58c06f1e59ec13dffa2151bec7fef478f0d491c263918c21fb38241e,
            "pinned then keccak"
        );
    }

    function testElseBranchPacksCommonWidth() public view {
        // cond == false selects b == 0x2233 (uint16), packed as 0x2233.
        require(
            target.packedHash(false) == keccak256(hex"2233"),
            "else-branch common width"
        );
        require(
            target.packedHash(false) ==
                0x0bea8c3dc955818b3f04b78631387a2a53f48726d725c56f6b3e3360c2011195,
            "pinned else keccak"
        );
    }
}
