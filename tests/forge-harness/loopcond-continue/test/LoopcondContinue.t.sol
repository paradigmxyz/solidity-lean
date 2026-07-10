// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {LoopcondContinueHarnessTarget} from "../src/LoopcondContinue.sol";

contract LoopcondContinueForgeTest {
    LoopcondContinueHarnessTarget private target =
        new LoopcondContinueHarnessTarget();

    function testForContinue() public view {
        require(target.forContinue() == 4, "for + call-cond + continue");
    }

    function testDoWhileContinue() public view {
        require(target.doWhileContinue() == 13, "do-while + call-cond + continue");
    }

    function testWhileContinue() public view {
        require(target.whileContinue() == 13, "while + call-cond + continue");
    }

    function testForMultiContinue() public view {
        require(target.forMultiContinue() == 6, "for + call-cond + multi continue");
    }

    function testForBodyCall() public view {
        require(target.forBodyCall() == 6, "for + call-cond + continue + body call");
    }

    function testForNestedIfContinue() public view {
        require(target.forNestedIfContinue() == 6, "for + call-cond + nested-if continue");
    }

    function testForContinueBreak() public view {
        require(target.forContinueBreak() == 4, "for + call-cond + continue + break");
    }
}
