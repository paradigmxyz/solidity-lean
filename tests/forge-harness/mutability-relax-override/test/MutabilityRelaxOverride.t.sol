// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {
    MutabilityRelaxOverrideBase,
    MutabilityRelaxOverrideHarnessTarget
} from "../src/MutabilityRelaxOverride.sol";

// Forge ground truth for G19: mutability-relaxing overrides dispatch to the
// override body. view->pure: tag(x)=x+2; nonpayable->view: bump(x)=x+20.
contract MutabilityRelaxOverrideForgeTest {
    function testRunTag() public {
        MutabilityRelaxOverrideHarnessTarget t =
            new MutabilityRelaxOverrideHarnessTarget();
        require(t.runTag(5) == 7, "runTag");
    }

    function testRunBump() public {
        MutabilityRelaxOverrideHarnessTarget t =
            new MutabilityRelaxOverrideHarnessTarget();
        require(t.runBump(5) == 25, "runBump");
    }

    // Virtual dispatch through a base-typed reference reaches the overrides.
    function testViaBaseReference() public {
        MutabilityRelaxOverrideBase b =
            new MutabilityRelaxOverrideHarnessTarget();
        require(b.tag(5) == 7, "tag via base");
        require(b.bump(5) == 25, "bump via base");
    }
}
