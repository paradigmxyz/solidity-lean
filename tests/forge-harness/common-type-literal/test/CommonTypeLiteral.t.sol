// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {CommonTypeLiteralHarnessTarget} from "../src/CommonTypeLiteral.sol";

contract CommonTypeLiteralForgeTest {
    function testMulWidenNoOverflow() public {
        CommonTypeLiteralHarnessTarget t = new CommonTypeLiteralHarnessTarget();
        require(t.mulWiden(200) == 60000, "mul60000");
    }

    function testMulWidenOverflowPanics() public {
        CommonTypeLiteralHarnessTarget t = new CommonTypeLiteralHarnessTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("mulWiden(uint8)", 255));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }

    function testAddReturnU16() public {
        CommonTypeLiteralHarnessTarget t = new CommonTypeLiteralHarnessTarget();
        require(t.addReturnU16(10) == 310, "add310");
    }

    function testMulU24NoOverflow() public {
        CommonTypeLiteralHarnessTarget t = new CommonTypeLiteralHarnessTarget();
        require(t.mulU24(100) == 7000000, "mul7e6");
    }

    function testMulU24OverflowPanics() public {
        CommonTypeLiteralHarnessTarget t = new CommonTypeLiteralHarnessTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("mulU24(uint16)", 1000));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
}
