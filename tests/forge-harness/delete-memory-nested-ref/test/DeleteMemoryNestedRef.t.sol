// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {DeleteMemNestedRefHarness} from "../src/DeleteMemoryNestedRef.sol";

contract DeleteMemoryNestedRefForgeTest {
    DeleteMemNestedRefHarness private harness = new DeleteMemNestedRefHarness();

    function testDeleteZeroesNestedArray() public view {
        (uint x, uint len) = harness.f();
        require(x == 0 && len == 0, "delete mem nested ref");
    }

    function testFreshAfterDelete() public view {
        (uint len, uint v) = harness.freshAfter();
        require(len == 2 && v == 5, "fresh array after delete");
    }

    function testDeleteFixedArrayOfDyn() public view {
        (uint a, uint b) = harness.g();
        require(a == 0 && b == 0, "delete fixed array of dyn");
    }

    function testDeleteNestedStruct() public view {
        (uint a, uint b, uint c) = harness.nested();
        require(a == 0 && b == 0 && c == 0, "delete nested struct");
    }

    function testAliasKeepsOldArray() public view {
        (uint bl, uint b0, uint sl) = harness.aliasCase();
        require(bl == 3 && b0 == 42 && sl == 0, "alias keeps old array");
    }

    function testValueStructUnchanged() public view {
        (uint a, uint b) = harness.valueStruct();
        require(a == 0 && b == 0, "value struct delete");
    }

    function testTopArrayUnchanged() public view {
        require(harness.topArray() == 0, "top array delete");
    }

    function testScalarLocalUnchanged() public view {
        require(harness.scalarLocal() == 0, "scalar local delete");
    }
}
