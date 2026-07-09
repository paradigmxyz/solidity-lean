// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {FreeFnNestedArgHarnessTarget} from "../src/FreeFnNestedArg.sol";

contract FreeFnNestedArgForgeTest {
    function testFreeNestedInFreeArg() public {
        FreeFnNestedArgHarnessTarget t = new FreeFnNestedArgHarnessTarget();
        require(t.run(5) == 11, "run");
    }

    function testFreeNestedInMemberArg() public {
        FreeFnNestedArgHarnessTarget t = new FreeFnNestedArgHarnessTarget();
        require(t.runMember(5) == 110, "runMember");
    }

    function testStructPassingFreeNested() public {
        FreeFnNestedArgHarnessTarget t = new FreeFnNestedArgHarnessTarget();
        require(t.runStruct() == 3, "runStruct");
    }

    function testExprStmtNestedFree() public {
        FreeFnNestedArgHarnessTarget t = new FreeFnNestedArgHarnessTarget();
        require(t.runExprStmt(5) == 7, "runExprStmt");
    }
}
