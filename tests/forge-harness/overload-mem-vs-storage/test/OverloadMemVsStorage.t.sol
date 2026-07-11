// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {OverloadMemVsStorageHarness} from "../src/OverloadMemVsStorage.sol";

contract OverloadMemVsStorageForgeTest {
    OverloadMemVsStorageHarness private harness = new OverloadMemVsStorageHarness();

    // Memory argument selects the memory overload: 3 + 100.
    function testCallMemory() public view {
        require(harness.callMemory() == 103, "memory overload dispatch");
    }
}
