// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ExtfnLocationErasureHarnessTarget} from "../src/ExtfnLocationErasure.sol";

contract ExtfnLocationErasureForgeTest {
    ExtfnLocationErasureHarnessTarget private harness = new ExtfnLocationErasureHarnessTarget();

    function testCallThroughPtr() public view {
        require(harness.callThroughPtr(39) == 42, "len 3 + seed 39");
    }

    function testCallThroughRetPtr() public view {
        require(harness.callThroughRetPtr(40) == 42, "seed 40 + len 2");
    }

    function testCallThroughCalldataRetPtr() public view {
        require(harness.callThroughCalldataRetPtr(40) == 42, "seed 40 + len 2 via calldata-return fn");
    }
}
