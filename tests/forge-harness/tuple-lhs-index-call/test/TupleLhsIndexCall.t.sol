// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {TupleLhsIndexCallHarnessTarget} from "../src/TupleLhsIndexCall.sol";

contract TupleLhsIndexCallForgeTest {
    function testArrayIndexCall() public {
        TupleLhsIndexCallHarnessTarget t = new TupleLhsIndexCallHarnessTarget();
        require(t.runArray() == 1, "arr logv");
        require(t.getXs(0) == 3, "arr xs0");
        require(t.getZ() == 4, "arr z");
    }

    function testMappingKeyCall() public {
        TupleLhsIndexCallHarnessTarget t = new TupleLhsIndexCallHarnessTarget();
        require(t.runMapping() == 7, "map logv");
        require(t.getM(2) == 8, "map m2");
        require(t.getZ() == 9, "map z");
    }

    function testEvalOrderRhsThenLhsIndex() public {
        TupleLhsIndexCallHarnessTarget t = new TupleLhsIndexCallHarnessTarget();
        // RHS left-to-right then LHS index left-to-right: 3,4,1,2 => 3412.
        require(t.runOrder() == 3412, "order logv");
        require(t.getXs(0) == 3, "order xs0");
        require(t.getYs(1) == 4, "order ys1");
    }

    function testCallInBothIndexAndRhs() public {
        TupleLhsIndexCallHarnessTarget t = new TupleLhsIndexCallHarnessTarget();
        // RHS rhs(3) (logv->3) then LHS index keyf() (logv->37).
        require(t.runBoth() == 37, "both logv");
        require(t.getXs(2) == 3, "both xs2");
        require(t.getZ() == 9, "both z");
    }
}
