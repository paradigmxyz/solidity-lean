// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {StorageArrayCopySignedFixedHarnessTarget} from "../src/StorageArrayCopySignedFixed.sol";

contract StorageArrayCopySignedFixedForgeTest {
    function testSignedWiden() public {
        StorageArrayCopySignedFixedHarnessTarget t = new StorageArrayCopySignedFixedHarnessTarget();
        (int256 a, int256 b, int256 len) = t.signedWiden();
        require(a == -5, "a");
        require(b == 127, "b");
        require(len == 2, "len");
    }
    function testFixedDestSigned() public {
        StorageArrayCopySignedFixedHarnessTarget t = new StorageArrayCopySignedFixedHarnessTarget();
        (int256 a, int256 b, int256 c, int256 d, int256 e) = t.fixedDestSigned();
        require(a == -1, "a");
        require(b == 100, "b");
        require(c == -128, "c");
        require(d == 0, "d");
        require(e == 0, "e");
    }
    function testFixedDestUnsigned() public {
        StorageArrayCopySignedFixedHarnessTarget t = new StorageArrayCopySignedFixedHarnessTarget();
        (uint256 a, uint256 b, uint256 c, uint256 d) = t.fixedDestUnsigned();
        require(a == 200, "a");
        require(b == 255, "b");
        require(c == 0, "c");
        require(d == 0, "d");
    }
}
