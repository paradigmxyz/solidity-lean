// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {RecursionRefSignaturesHarnessTarget} from "../src/RecursionRefSignatures.sol";

contract RecursionRefSignaturesForgeTest {
    RecursionRefSignaturesHarnessTarget private target =
        new RecursionRefSignaturesHarnessTarget();

    function testViaStorageRecursion() public {
        require(target.viaStorageRecursion() == 60, "storage recursion");
    }

    function testViaMemoryRecursion() public view {
        require(target.viaMemoryRecursion() == 15099, "memory recursion");
    }
}
