// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {FnptrInternalEqDerivedHarnessTarget} from "../src/FnptrInternalEqDerived.sol";

// Forge ground truth for internal function-pointer equality/inequality on
// ternary-initialized and storage-read pointers (#53, FP-EQ-2).
contract FnptrInternalEqDerivedForgeTest {
    function newTarget() internal returns (FnptrInternalEqDerivedHarnessTarget) {
        return new FnptrInternalEqDerivedHarnessTarget();
    }

    function testTernEqTrue() public {
        require(newTarget().ternEq(true) == true, "ternEq(true)");
    }

    function testTernEqFalse() public {
        require(newTarget().ternEq(false) == false, "ternEq(false)");
    }

    function testTernNeTrue() public {
        require(newTarget().ternNe(true) == false, "ternNe(true)");
    }

    function testTernNeFalse() public {
        require(newTarget().ternNe(false) == true, "ternNe(false)");
    }

    function testStoreThenEqSame() public {
        require(newTarget().storeThenEqSame() == true, "storeThenEqSame");
    }

    function testStoreThenEqDiff() public {
        require(newTarget().storeThenEqDiff() == false, "storeThenEqDiff");
    }

    function testStoreThenNe() public {
        require(newTarget().storeThenNe() == true, "storeThenNe");
    }
}
