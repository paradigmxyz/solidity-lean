// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {FnValueShadowingHarnessTarget} from "../src/FnValueShadowing.sol";

contract FnValueShadowingForgeTest {
    FnValueShadowingHarnessTarget private target =
        new FnValueShadowingHarnessTarget();

    function testParamShadow() public view {
        require(target.go(5) == 6, "param x must shadow function x");
    }

    function testLocalShadow() public view {
        require(target.localShadow() == 14, "local x must shadow function x");
    }

    function testLoopShadow() public view {
        require(target.loopShadow(4) == 6, "loop binding x must shadow function x");
    }

    function testNestedScopes() public view {
        require(target.nestedScopes() == 47, "function x resolves after block");
    }

    function testSelectTrue() public view {
        require(target.select(true) == 11, "fn-pointer select true");
    }

    function testSelectFalse() public view {
        require(target.select(false) == 22, "fn-pointer select false");
    }
}
