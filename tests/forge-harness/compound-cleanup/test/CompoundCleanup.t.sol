// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {CompoundCleanupHarnessTarget} from "../src/CompoundCleanup.sol";

contract CompoundCleanupForgeTest {
    CompoundCleanupHarnessTarget private target =
        new CompoundCleanupHarnessTarget();

    function testShlTruncates() public view {
        require(target.shlTrunc() == 0, "uint8 16 <<= 4 must truncate to 0");
    }

    function testAddOverflowPanics() public {
        try target.addOverflow() returns (uint8) {
            revert("expected += overflow panic");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong += overflow panic");
        }
    }

    function testAddUncheckedWraps() public {
        require(target.addUncheckedWrap() == 44, "unchecked += must wrap to 44");
    }

    function testMulOverflowPanics() public {
        try target.mulOverflow() returns (uint8) {
            revert("expected *= overflow panic");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong *= overflow panic");
        }
    }

    function testAddNoOverflow() public view {
        require(target.addNoOverflow() == 155, "in-range += must equal 155");
    }

    function testMapOverflowPanics() public {
        try target.mapOverflow() returns (uint8) {
            revert("expected mapping += overflow panic");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong mapping += overflow panic");
        }
    }

    function testMapUncheckedWraps() public {
        require(target.mapUncheckedWrap() == 4, "unchecked mapping += must wrap to 4");
    }

    function testArrOverflowPanics() public {
        try target.arrOverflow() returns (uint8) {
            revert("expected array += overflow panic");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong array += overflow panic");
        }
    }

    function testStructOverflowPanics() public {
        try target.structOverflow() returns (uint8) {
            revert("expected struct += overflow panic");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong struct += overflow panic");
        }
    }

    function testWideAddControl() public view {
        require(target.wideAddControl() == 3000000, "uint256 += must equal 3000000");
    }
}
