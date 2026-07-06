// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {StorageCounterHarnessTarget} from "../src/StorageCounter.sol";

contract StorageCounterForgeTest {
    StorageCounterHarnessTarget private target =
        new StorageCounterHarnessTarget();

    function testInitialValueIsZero() public view {
        require(target.read() == 0, "initial value");
    }

    function testIncThenRead() public {
        target.inc();
        require(target.read() == 1, "incremented value");
    }

    function testAddAfterInc() public {
        target.inc();
        target.add(41);
        require(target.read() == 42, "added value");
    }
}
