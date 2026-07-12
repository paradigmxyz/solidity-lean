// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {StorageRefEarlyBindTarget} from "../src/StorageRefEarlyBind.sol";

contract StorageRefEarlyBindForgeTest {
    function newTarget() internal returns (StorageRefEarlyBindTarget) {
        return new StorageRefEarlyBindTarget();
    }

    function testT1() public { require(newTarget().t1() == 0, "t1"); }
    function testT2() public { require(newTarget().t2() == 9, "t2"); }
    function testT3Code() public { require(newTarget().t3code() == 0x32, "t3code"); }
    function testT4() public { require(newTarget().t4() == 33, "t4"); }
    function testT5() public { require(newTarget().t5() == 88, "t5"); }
    function testT6() public { require(newTarget().t6() == 5, "t6"); }
    function testT7() public { require(newTarget().t7() == 42, "t7"); }
    function testT8() public { require(newTarget().t8() == 88, "t8"); }
    function testT9() public { require(newTarget().t9() == 55, "t9"); }
}
