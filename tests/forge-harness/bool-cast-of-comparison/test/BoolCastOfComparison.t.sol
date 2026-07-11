// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {BoolCastOfComparisonTarget} from "../src/BoolCastOfComparison.sol";

contract BoolCastOfComparisonForgeTest {
    function testEqCast() public {
        BoolCastOfComparisonTarget t = new BoolCastOfComparisonTarget();
        require(t.eqCast() == false, "eqCast");
    }
    function testLtCast() public {
        BoolCastOfComparisonTarget t = new BoolCastOfComparisonTarget();
        require(t.ltCast() == true, "ltCast");
    }
    function testAndCast() public {
        BoolCastOfComparisonTarget t = new BoolCastOfComparisonTarget();
        require(t.andCast() == true, "andCast");
    }
    function testNotCast() public {
        BoolCastOfComparisonTarget t = new BoolCastOfComparisonTarget();
        require(t.notCast() == true, "notCast");
    }
    function testArithCast() public {
        BoolCastOfComparisonTarget t = new BoolCastOfComparisonTarget();
        require(t.arithCast() == 3, "arithCast");
    }
    function testShiftCast() public {
        BoolCastOfComparisonTarget t = new BoolCastOfComparisonTarget();
        require(t.shiftCast() == 8, "shiftCast");
    }
}
