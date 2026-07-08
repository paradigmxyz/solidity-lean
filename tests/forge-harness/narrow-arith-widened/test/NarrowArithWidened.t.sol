// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {NarrowArithWidenedHarnessTarget} from "../src/NarrowArithWidened.sol";

contract NarrowArithWidenedForgeTest {
    function testAddNoOverflow() public {
        NarrowArithWidenedHarnessTarget t = new NarrowArithWidenedHarnessTarget();
        require(t.addU8toU16(100, 55) == 155, "add155");
    }
    function testAddOverflowPanics() public {
        NarrowArithWidenedHarnessTarget t = new NarrowArithWidenedHarnessTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("addU8toU16(uint8,uint8)", 200, 100));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
    function testMulOverflowPanics() public {
        NarrowArithWidenedHarnessTarget t = new NarrowArithWidenedHarnessTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("mulU8toU16(uint8,uint8)", 20, 20));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
    function testAddSignedNoOverflow() public {
        NarrowArithWidenedHarnessTarget t = new NarrowArithWidenedHarnessTarget();
        require(t.addI8toI16(100, 20) == 120, "s120");
    }
    function testAddSignedOverflowPanics() public {
        NarrowArithWidenedHarnessTarget t = new NarrowArithWidenedHarnessTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("addI8toI16(int8,int8)", 100, 100));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
    function testWidenedOperandsNoPanic() public {
        NarrowArithWidenedHarnessTarget t = new NarrowArithWidenedHarnessTarget();
        require(t.addWidenedOperands(200, 100) == 300, "wide300");
    }
}
