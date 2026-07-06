// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {CheckedArithmeticHarnessTarget} from "../src/CheckedArithmetic.sol";

contract CheckedArithmeticForgeTest {
    CheckedArithmeticHarnessTarget private target =
        new CheckedArithmeticHarnessTarget();

    function testAddOverflowPanics() public {
        try target.addOverflow(1) returns (uint256) {
            revert("expected overflow panic");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong overflow panic");
        }
    }

    function testUncheckedAddWraps() public view {
        uint256 result = target.uncheckedAddWrap(1);
        require(result == 0, "unchecked add did not wrap");
    }

    function testDivisionByZeroPanics() public {
        try target.divide(7, 0) returns (uint256) {
            revert("expected division-by-zero panic");
        } catch Panic(uint256 code) {
            require(code == 0x12, "wrong division panic");
        }
    }
}
