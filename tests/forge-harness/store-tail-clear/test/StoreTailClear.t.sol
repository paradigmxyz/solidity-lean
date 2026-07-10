// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {StoreTailClearHarnessTarget} from "../src/StoreTailClear.sol";

contract StoreTailClearForgeTest {
    function testStructShrink() public {
        StoreTailClearHarnessTarget t = new StoreTailClearHarnessTarget();
        (uint256 len, uint256 e0, uint256 e1) = t.structShrink();
        require(len == 2, "len");
        require(e0 == 100, "e0");
        require(e1 == 200, "e1");
    }

    function testStorageToStorageShrink() public {
        StoreTailClearHarnessTarget t = new StoreTailClearHarnessTarget();
        (uint256 len, uint256 e0, uint256 e1) = t.storageToStorageShrink();
        require(len == 2, "len");
        require(e0 == 111, "e0");
        require(e1 == 222, "e1");
    }

    function testFixedArrayDynShrink() public {
        StoreTailClearHarnessTarget t = new StoreTailClearHarnessTarget();
        (uint256 l0, uint256 e01, uint256 l1, uint256 e11) = t.fixedArrayDynShrink();
        require(l0 == 2, "l0");
        require(e01 == 101, "e01");
        require(l1 == 2, "l1");
        require(e11 == 201, "e11");
    }

    function testFixedArrayStructShrink() public {
        StoreTailClearHarnessTarget t = new StoreTailClearHarnessTarget();
        (uint256 l0, uint256 e01, uint256 l1, uint256 e11) = t.fixedArrayStructShrink();
        require(l0 == 2, "l0");
        require(e01 == 101, "e01");
        require(l1 == 2, "l1");
        require(e11 == 201, "e11");
    }

    function testStructGrow() public {
        StoreTailClearHarnessTarget t = new StoreTailClearHarnessTarget();
        (uint256 len, uint256 e2, uint256 e3) = t.structGrow();
        require(len == 4, "len");
        require(e2 == 3, "e2");
        require(e3 == 4, "e3");
    }
}
