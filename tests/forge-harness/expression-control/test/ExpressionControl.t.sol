// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ExpressionControlHarnessTarget} from "../src/ExpressionControl.sol";

contract ExpressionControlForgeTest {
    ExpressionControlHarnessTarget private target =
        new ExpressionControlHarnessTarget();

    function testShortCircuitSideEffects() public view {
        require(target.shortCircuit() == 1118, "short circuit");
    }

    function testTernaryThenBranch() public view {
        require(target.ternarySelect(true) == 707, "then");
    }

    function testTernaryElseBranch() public view {
        require(target.ternarySelect(false) == 909, "else");
    }
}
