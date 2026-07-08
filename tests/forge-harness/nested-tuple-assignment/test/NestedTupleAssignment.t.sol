// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {NestedTupleAssignmentHarnessTarget} from "../src/NestedTupleAssignment.sol";

contract NestedTupleAssignmentForgeTest {
    NestedTupleAssignmentHarnessTarget private target =
        new NestedTupleAssignmentHarnessTarget();

    function testNestedLit() public view {
        require(target.nestedLit(3) == 345, "nestedLit");
    }

    function testNestedRight() public view {
        require(target.nestedRight(3) == 345, "nestedRight");
    }

    function testNestedSwap() public view {
        require(target.nestedSwap(3) == 453, "nestedSwap");
    }

    function testNestedHole() public view {
        require(target.nestedHole(3) == 35, "nestedHole");
    }
}
