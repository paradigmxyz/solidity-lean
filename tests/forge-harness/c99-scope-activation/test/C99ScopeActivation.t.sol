// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {C99ScopeActivationHarnessTarget} from "../src/C99ScopeActivation.sol";

// Forge ground truth for G21: C99 activation values.
contract C99ScopeActivationForgeTest {
    function newTarget() internal returns (C99ScopeActivationHarnessTarget) {
        return new C99ScopeActivationHarnessTarget();
    }

    function testBlockActivation() public {
        require(newTarget().blockActivation() == 1100, "blockActivation");
    }

    function testSelfInitFromOuter() public {
        require(newTarget().selfInitFromOuter() == 6, "selfInitFromOuter");
    }
}
