// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {CF2RevertPruningHarnessTarget} from "../src/CF2RevertPruning.sol";

contract CF2RevertPruningForgeTest {
    CF2RevertPruningHarnessTarget private target =
        new CF2RevertPruningHarnessTarget();

    function testHelperRevertPointerReturn() public {
        target.seed();
        require(target.pickLength() == 3, "length");
        require(target.pickAt(0) == 11, "at0");
        require(target.pickAt(1) == 22, "at1");
        require(target.pickAt(2) == 33, "at2");
    }
}
