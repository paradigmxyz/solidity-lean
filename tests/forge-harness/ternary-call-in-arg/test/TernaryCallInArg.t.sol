// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {TernaryCallInArgHarnessTarget} from "../src/TernaryCallInArg.sol";

contract TernaryCallInArgForgeTest {
    TernaryCallInArgHarnessTarget private target =
        new TernaryCallInArgHarnessTarget();

    function testCallThenTrue() public view {
        require(target.callThen(true) == 2, "callThen(true)");
    }

    function testCallThenFalse() public view {
        require(target.callThen(false) == 4, "callThen(false)");
    }

    function testCallElseTrue() public view {
        require(target.callElse(true) == 18, "callElse(true)");
    }

    function testCallElseFalse() public view {
        require(target.callElse(false) == 4, "callElse(false)");
    }

    function testCallBothTrue() public view {
        require(target.callBoth(true) == 2, "callBoth(true)");
    }

    function testCallBothFalse() public view {
        require(target.callBoth(false) == 4, "callBoth(false)");
    }

    function testAssignRhsTrue() public view {
        require(target.assignRhs(true) == 2, "assignRhs(true)");
    }

    function testAssignRhsFalse() public view {
        require(target.assignRhs(false) == 4, "assignRhs(false)");
    }

    function testOrderTwoArgTrue() public view {
        require(target.orderTwoArg(true) == 12, "orderTwoArg(true)");
    }

    function testOrderTwoArgFalse() public view {
        require(target.orderTwoArg(false) == 13, "orderTwoArg(false)");
    }

    function testLitTernaryArgTrue() public view {
        require(target.litTernaryArg(true) == 2, "litTernaryArg(true)");
    }

    function testLitTernaryArgFalse() public view {
        require(target.litTernaryArg(false) == 4, "litTernaryArg(false)");
    }

    function testBinaryOperandTrue() public view {
        require(target.binaryOperand(true) == 11, "binaryOperand(true)");
    }

    function testBinaryOperandFalse() public view {
        require(target.binaryOperand(false) == 12, "binaryOperand(false)");
    }

    function testRequireCondTrue() public view {
        require(target.requireCond(true) == 42, "requireCond(true)");
    }

    function testRequireCondFalse() public view {
        require(target.requireCond(false) == 42, "requireCond(false)");
    }

    function testReturnTernaryTrue() public view {
        require(target.returnTernary(true) == 1, "returnTernary(true)");
    }

    function testReturnTernaryFalse() public view {
        require(target.returnTernary(false) == 2, "returnTernary(false)");
    }
}
