// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {TernaryLiteralMobileTypeHarnessTarget} from "../src/TernaryLiteralMobileType.sol";

contract TernaryLiteralMobileTypeForgeTest {
    TernaryLiteralMobileTypeHarnessTarget private target =
        new TernaryLiteralMobileTypeHarnessTarget();

    function testNarrowAssign() public view {
        require(target.narrowAssign(true) == 63, "narrow true");
        require(target.narrowAssign(false) == 255, "narrow false");
    }

    function testWidenAssign() public view {
        require(target.widenAssign(true) == 63, "widen true");
        require(target.widenAssign(false) == 255, "widen false");
    }

    function testWidthPanicTrueOk() public view {
        require(target.widthPanic(true) == 64, "63+1 in uint8");
    }

    function testWidthPanicFalseOverflows() public {
        try target.widthPanic(false) returns (uint8) {
            revert("expected uint8 overflow panic");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong overflow panic");
        }
    }

    function testUint16Common() public view {
        require(target.uint16Common(true) == 300, "uint16 true");
        require(target.uint16Common(false) == 400, "uint16 false");
    }
}
