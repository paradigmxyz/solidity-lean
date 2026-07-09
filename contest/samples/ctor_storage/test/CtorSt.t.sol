// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {CtorSt} from "../src/CtorSt.sol";

contract CtorStTest {
    function test_run() public {
        CtorSt c = new CtorSt();
        require(c.run(7) == 40, "sum");
        require(c.slot0() == 11 && c.slot1() == 22 && c.slot2() == 7, "slots");
        require(c.m(7) == 107, "mapping");
    }
}
