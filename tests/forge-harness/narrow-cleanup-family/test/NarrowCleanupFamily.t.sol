// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {NarrowCleanupFamilyHarnessTarget} from "../src/NarrowCleanupFamily.sol";

contract NarrowCleanupFamilyForgeTest {
    NarrowCleanupFamilyHarnessTarget private target =
        new NarrowCleanupFamilyHarnessTarget();

    // #182 for-init counter overflow -> Panic 0x11.
    function testForCounterOverflowPanics() public {
        try target.forCounterOverflow() returns (uint256) {
            revert("expected for-counter overflow");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong panic");
        }
    }

    function testForCounterSafe() public view {
        require(target.forCounterSafe() == 10, "safe loop counts 10");
    }

    function testForCounterUncheckedWrap() public view {
        require(target.forCounterUncheckedWrap() == 11, "unchecked wrap counts 11");
    }

    // #183 push of narrow checked arithmetic overflow -> Panic 0x11.
    function testPushAddOverflowPanics() public {
        try target.pushAdd(200, 100) returns (uint8) {
            revert("expected push add overflow");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong panic");
        }
    }

    function testPushCastTruncates() public {
        require(target.pushCast(300) == 44, "300 truncates to 44");
    }

    function testPushSafe() public {
        require(target.pushSafe(7) == 7, "safe push");
    }

    // #183 nested 2d push overflow -> Panic 0x11.
    function testPush2dAddOverflowPanics() public {
        try target.push2dAdd(200, 100) returns (uint8) {
            revert("expected 2d push add overflow");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong panic");
        }
    }

    // #184 struct-ctor field on assign overflow -> Panic 0x11.
    function testStructAssignAddOverflowPanics() public {
        try target.structAssignAdd(200, 100) returns (uint8) {
            revert("expected struct assign overflow");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong panic");
        }
    }

    // #184 struct-ctor field on vardecl overflow -> Panic 0x11.
    function testStructVarDeclAddOverflowPanics() public {
        try target.structVarDeclAdd(200, 100) returns (uint8) {
            revert("expected struct vardecl overflow");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong panic");
        }
    }

    function testStructCastTruncates() public {
        require(target.structCast(300) == 44, "300 truncates to 44");
    }

    // isolation: direct struct return overflow -> Panic 0x11.
    function testStructReturnAddOverflowPanics() public {
        try target.structReturnAdd(200, 100) returns (
            NarrowCleanupFamilyHarnessTarget.S memory
        ) {
            revert("expected struct return overflow");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong panic");
        }
    }
}
