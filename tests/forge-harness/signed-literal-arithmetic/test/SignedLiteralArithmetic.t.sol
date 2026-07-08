// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {SignedLiteralArithmeticHarnessTarget} from "../src/SignedLiteralArithmetic.sol";

contract SignedLiteralArithmeticForgeTest {
    SignedLiteralArithmeticHarnessTarget private target =
        new SignedLiteralArithmeticHarnessTarget();

    function testDivPositiveLiteral() public view {
        require(target.divPosLit(5e18) == 5, "5e18 / 1e18");
        require(target.divPosLit(-5e18) == -5, "-5e18 / 1e18");
        // truncation toward zero
        require(target.divPosLit(-1) == 0, "-1 / 1e18");
    }

    function testDivNegativeLiteral() public view {
        require(target.divNegLit(7) == -3, "7 / -2 trunc toward zero");
        require(target.divNegLit(-7) == 3, "-7 / -2 trunc toward zero");
    }

    function testDivIntMinPanics() public {
        try target.divIntMin() returns (int256) {
            revert("expected INT_MIN/-1 panic");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong overflow panic");
        }
    }

    function testNeighborOps() public view {
        require(target.mulLit(4) == 12, "4 * 3");
        require(target.addLit(-2) == 3, "-2 + 5");
        require(target.subLit(-2) == -7, "-2 - 5");
        require(target.modLit(-8) == -1, "-8 % 7 trunc");
    }
}
