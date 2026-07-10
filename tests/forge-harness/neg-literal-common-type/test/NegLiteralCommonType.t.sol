// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {NegLiteralCommonTypeHarnessTarget} from "../src/NegLiteralCommonType.sol";

contract NegLiteralCommonTypeForgeTest {
    function testMulI16FitsNegative() public {
        NegLiteralCommonTypeHarnessTarget t = new NegLiteralCommonTypeHarnessTarget();
        require(t.mulI16(100) == -30000, "mulI16(100)");
    }

    function testMulI16FitsPositive() public {
        NegLiteralCommonTypeHarnessTarget t = new NegLiteralCommonTypeHarnessTarget();
        require(t.mulI16(-100) == 30000, "mulI16(-100)");
    }

    function testMulI16UnderflowPanics() public {
        NegLiteralCommonTypeHarnessTarget t = new NegLiteralCommonTypeHarnessTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("mulI16(int16)", int16(200)));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }

    function testMulI16OverflowPanics() public {
        NegLiteralCommonTypeHarnessTarget t = new NegLiteralCommonTypeHarnessTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("mulI16(int16)", int16(-200)));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }

    function testMulI8Neg1Fits() public {
        NegLiteralCommonTypeHarnessTarget t = new NegLiteralCommonTypeHarnessTarget();
        require(t.mulI8Neg1(100) == -100, "mulI8Neg1(100)");
    }

    function testMulI8Neg1MinNegationPanics() public {
        NegLiteralCommonTypeHarnessTarget t = new NegLiteralCommonTypeHarnessTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("mulI8Neg1(int8)", int8(-128)));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }

    function testAddI16Fits() public {
        NegLiteralCommonTypeHarnessTarget t = new NegLiteralCommonTypeHarnessTarget();
        require(t.addI16Neg300(100) == -200, "addI16Neg300(100)");
    }

    function testAddI16UnderflowPanics() public {
        NegLiteralCommonTypeHarnessTarget t = new NegLiteralCommonTypeHarnessTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("addI16Neg300(int16)", int16(-32700)));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }

    function testLitMulLeftFits() public {
        NegLiteralCommonTypeHarnessTarget t = new NegLiteralCommonTypeHarnessTarget();
        require(t.litMulLeft(50) == -15000, "litMulLeft(50)");
    }

    function testLitMulLeftOverflowPanics() public {
        NegLiteralCommonTypeHarnessTarget t = new NegLiteralCommonTypeHarnessTarget();
        (bool ok, bytes memory data) = address(t).call(abi.encodeWithSignature("litMulLeft(int16)", int16(-500)));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
}
