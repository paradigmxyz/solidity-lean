// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {NarrowBitwiseCleanupHarnessTarget} from "../src/NarrowBitwiseCleanup.sol";

contract NarrowBitwiseCleanupForgeTest {
    NarrowBitwiseCleanupHarnessTarget private target =
        new NarrowBitwiseCleanupHarnessTarget();

    function testWidenedLeftShiftUnsigned() public view {
        require(target.a(255) == 240, "uint8 255 << 4 widened must be 240");
    }

    function testWidenedLeftShiftSigned() public view {
        require(target.b(64) == -128, "int8 64 << 1 widened must be -128");
    }

    function testNotNarrowUnsignedSameWidth() public view {
        require(target.c(0) == 255, "~uint8(0) must be 255, not a panic");
    }

    function testNotNarrowUnsignedWidened() public view {
        require(target.d(0) == 255, "~uint8(0) widened must be 255, not a panic");
    }

    function testSameWidthLeftShiftUnchanged() public view {
        require(target.shlSameWidth(255) == 240, "same-width uint8 << 4 must be 240");
    }

    function testCheckedArithmeticStillPanics() public {
        try target.addOverflow(200) returns (uint8) {
            revert("expected checked + overflow panic");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong checked + overflow panic code");
        }
    }

    function testNotFullWidthUnchanged() public view {
        require(target.notWide() == type(uint256).max, "~uint256(0) must be 2^256-1");
    }

    function testNotNarrowSignedUnchanged() public view {
        require(target.notInt(5) == -6, "~int8(5) must be -6");
    }
}
