// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {CallPositionHarnessTarget} from "../src/CallPosition.sol";

contract CallPositionForgeTest {
    CallPositionHarnessTarget private target = new CallPositionHarnessTarget();

    function testForCondInternalValue() public view {
        require(target.forCondInternal() == 10, "for-cond internal");
    }

    function testWhileCondInternal() public view {
        require(target.whileCondInternal() == 10, "while-cond internal");
    }

    function testWhileContinueInternal() public view {
        require(target.whileContinueInternal() == 13, "while continue internal");
    }

    function testDoWhileCondInternal() public view {
        require(target.doWhileCondInternal() == 10, "do-while cond internal");
    }

    function testNestedForCondInternal() public view {
        require(target.nestedForCondInternal() == 5, "nested for-cond internal");
    }

    function testWhileBareExternal() public view {
        require(target.whileBareExternal() == 10, "while bare external");
    }
}
