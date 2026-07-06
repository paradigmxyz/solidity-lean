// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {LoopControlHarnessTarget} from "../src/LoopControl.sol";

contract LoopControlForgeTest {
    LoopControlHarnessTarget private target = new LoopControlHarnessTarget();

    function testWhileContinueAndBreak() public view {
        require(target.whileSum(10) == 12, "while");
    }

    function testForContinueAndBreak() public view {
        require(target.forSum(10) == 12, "for");
    }

    function testForLimitStopsBeforeBreak() public view {
        require(target.forSum(5) == 7, "for limit");
    }
}
