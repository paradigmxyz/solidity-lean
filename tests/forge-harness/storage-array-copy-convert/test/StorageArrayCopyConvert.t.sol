// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {StorageArrayCopyConvertHarnessTarget} from "../src/StorageArrayCopyConvert.sol";

contract StorageArrayCopyConvertForgeTest {
    function testWidenU8toU16() public {
        StorageArrayCopyConvertHarnessTarget t = new StorageArrayCopyConvertHarnessTarget();
        (uint256 a, uint256 b, uint256 len) = t.widenU8toU16();
        require(a == 255, "a");
        require(b == 7, "b");
        require(len == 2, "len");
    }

    function testWidenU8toU256() public {
        StorageArrayCopyConvertHarnessTarget t = new StorageArrayCopyConvertHarnessTarget();
        (uint256 a, uint256 b, uint256 c, uint256 len) = t.widenU8toU256();
        require(a == 1, "a");
        require(b == 2, "b");
        require(c == 3, "c");
        require(len == 3, "len");
    }

    function testShorterClearsTail() public {
        StorageArrayCopyConvertHarnessTarget t = new StorageArrayCopyConvertHarnessTarget();
        (uint256 len, uint256 i2, uint256 i4) = t.shorterClearsTail();
        require(len == 2, "len");
        require(i2 == 0, "i2");
        require(i4 == 0, "i4");
    }
}
