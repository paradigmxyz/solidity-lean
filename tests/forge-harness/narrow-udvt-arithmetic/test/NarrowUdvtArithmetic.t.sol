// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {NarrowUdvtArithmeticHarnessTarget} from "../src/NarrowUdvtArithmetic.sol";

contract NarrowUdvtArithmeticForgeTest {
    NarrowUdvtArithmeticHarnessTarget private target =
        new NarrowUdvtArithmeticHarnessTarget();

    function testAddU8InRange() public view {
        require(target.addU8(100, 55) == 155, "100+55");
    }

    function testAddU8OverflowPanics() public {
        try target.addU8(200, 100) returns (uint8) {
            revert("expected uint8 overflow");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong panic");
        }
    }

    function testAddI8OverflowPanics() public {
        try target.addI8(100, 100) returns (int8) {
            revert("expected int8 overflow");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong panic");
        }
    }

    function testSubI8UnderflowPanics() public {
        try target.subI8(-100, 100) returns (int8) {
            revert("expected int8 underflow");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong panic");
        }
    }

    function testAddI8InRange() public view {
        require(target.addI8(-100, 50) == -50, "-100+50");
    }

    function testAddU8UncheckedWraps() public view {
        require(target.addU8Unchecked(200, 100) == 44, "200+100 wraps to 44");
    }

    function testAddU8OperatorOverflowPanics() public {
        try target.addU8Operator(200, 100) returns (uint8) {
            revert("expected operator uint8 overflow");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong panic");
        }
    }

    function testAddBig() public view {
        require(target.addBig(5, 6) == 11, "big 5+6");
    }
}
