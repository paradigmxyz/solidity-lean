// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {EnumOrderedCompareHarnessTarget} from "../src/EnumOrderedCompare.sol";

contract EnumOrderedCompareForgeTest {
    EnumOrderedCompareHarnessTarget internal target;

    function setUp() public {
        target = new EnumOrderedCompareHarnessTarget();
    }

    function testLt() external {
        require(target.ltTrue(), "ltTrue");
        require(!target.ltFalse(), "ltFalse");
    }

    function testGt() external {
        require(target.gtTrue(), "gtTrue");
        require(!target.gtFalse(), "gtFalse");
    }

    function testLe() external {
        require(target.leTrueLt(), "leTrueLt");
        require(target.leTrueEq(), "leTrueEq");
        require(!target.leFalse(), "leFalse");
    }

    function testGe() external {
        require(target.geTrue(), "geTrue");
        require(target.geTrueEq(), "geTrueEq");
        require(!target.geFalse(), "geFalse");
    }

    function testGate() external {
        // s = Init (0) < Done (2) => true
        require(target.gate(EnumOrderedCompareHarnessTarget.State.Init), "gateInit");
        // s = Running (1) < Done (2) => true
        require(target.gate(EnumOrderedCompareHarnessTarget.State.Running), "gateRunning");
        // s = Done (2) < Done (2) => false
        require(!target.gate(EnumOrderedCompareHarnessTarget.State.Done), "gateDone");
    }
}
