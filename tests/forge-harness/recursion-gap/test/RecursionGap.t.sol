// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {RecursionGapHarnessTarget} from "../src/RecursionGap.sol";

// solc/Forge accept and execute recursion and deep static call nesting; these
// pass today. They are the differential counterpart to the Lean witnesses in
// the manifest, which pin the CURRENT Lean rejection (elaboration returns none)
// and flip to these same values at stage 5 of the function-boundary refactor.
contract RecursionGapForgeTest {
    RecursionGapHarnessTarget private target =
        new RecursionGapHarnessTarget();

    function testFactorial() public view {
        require(target.factorial(5) == 120, "factorial");
    }

    function testDeepRecursion() public view {
        require(target.sumTo(70) == 2485, "sumTo");
    }

    function testDeepStaticChain() public view {
        require(target.deepChain() == 70, "deepChain");
    }
}
