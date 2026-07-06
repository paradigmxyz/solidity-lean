// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {FunctionCallHarnessTarget} from "../src/FunctionCalls.sol";

contract FunctionCallsForgeTest {
    FunctionCallHarnessTarget private target =
        new FunctionCallHarnessTarget();

    function testNamedFallthrough() public view {
        require(target.namedFallthrough(7) == 14, "fallthrough");
    }

    function testDefaultNamedReturn() public view {
        require(target.defaultNamedReturn() == 0, "default return");
    }

    function testNamedArgumentOrder() public view {
        require(target.namedArgumentOrder(9) == 409, "named args");
    }
}
