// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import { MidD } from "../src/ConstructorIntermediateBaseArgs.sol";

contract ConstructorIntermediateBaseArgsForgeTest {
    // MidD supplies MidC(5); MidC supplies MidB(y * 2) with y == 5, so the
    // intermediate contract's modifier-supplied base argument evaluates to 10.
    function testIntermediateBaseArgs() public {
        MidD t = new MidD();
        require(t.cVal() == 5, "cVal from MidD(MidC(5))");
        require(t.bVal() == 10, "bVal from MidC(MidB(y * 2))");
    }
}
