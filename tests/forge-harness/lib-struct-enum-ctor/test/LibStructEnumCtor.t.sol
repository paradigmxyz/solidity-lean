// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {LibStructEnumCtorHarnessTarget} from "../src/LibStructEnumCtor.sol";

contract LibStructEnumCtorForgeTest {
    LibStructEnumCtorHarnessTarget private harness = new LibStructEnumCtorHarnessTarget();

    function testDirect() public view {
        require(harness.direct(2) == 12, "Auto(2) + 10");
        require(harness.direct(0) == 10, "Off(0) + 10");
    }

    function testViaLib() public view {
        require(harness.viaLib(2) == 12, "lib-internal unqualified ctor");
    }

    function testViaLibQ() public view {
        require(harness.viaLibQ(1) == 11, "lib-internal qualified ctor");
    }

    function testNamed() public view {
        require(harness.named(2) == 12, "named-args qualified ctor");
    }

    function testForeignEnumField() public view {
        require(harness.foreignEnumField(1) == 11, "foreign library enum field");
    }

    function testStoredWrite() public {
        require(harness.storedWrite(2) == 12, "storage write of ctor value");
    }
}
