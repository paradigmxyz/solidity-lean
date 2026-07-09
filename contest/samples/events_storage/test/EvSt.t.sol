// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {EvSt} from "../src/EvSt.sol";

contract EvStTest {
    function test_run() public {
        EvSt e = new EvSt();
        require(e.run(5) == 8, "ret");
        require(e.slot0() == 5, "s0");
        require(e.slot1() == 6, "s1");
    }
}
