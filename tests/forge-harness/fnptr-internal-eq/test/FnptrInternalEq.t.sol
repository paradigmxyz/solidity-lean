// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {FnptrInternalEqHarnessTarget} from "../src/FnptrInternalEq.sol";

// Forge ground truth for internal function-pointer equality/inequality (#50).
contract FnptrInternalEqForgeTest {
    function newTarget() internal returns (FnptrInternalEqHarnessTarget) {
        return new FnptrInternalEqHarnessTarget();
    }

    function testEqSame() public {
        require(newTarget().eqSame() == true, "eqSame");
    }

    function testEqDiff() public {
        require(newTarget().eqDiff() == false, "eqDiff");
    }

    function testNeDiff() public {
        require(newTarget().neDiff() == true, "neDiff");
    }

    function testNeSame() public {
        require(newTarget().neSame() == false, "neSame");
    }

    function testEqTwoSame() public {
        require(newTarget().eqTwoSame() == true, "eqTwoSame");
    }

    function testEqAfterReassign() public {
        require(newTarget().eqAfterReassign() == true, "reassign identity");
    }
}
