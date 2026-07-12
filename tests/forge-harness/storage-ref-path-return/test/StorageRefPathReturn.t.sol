// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {StorageRefPathReturnTarget} from "../src/StorageRefPathReturn.sol";

contract StorageRefPathReturnForgeTest {
    function newTarget() internal returns (StorageRefPathReturnTarget) {
        return new StorageRefPathReturnTarget();
    }

    function testT1() public { require(newTarget().t1() == 42, "t1"); }
    function testT2() public { require(newTarget().t2() == 77, "t2"); }
    function testT3() public { require(newTarget().t3() == 88, "t3"); }
    function testT4() public { require(newTarget().t4() == 55, "t4"); }
    function testT5() public { require(newTarget().t5() == 42, "t5"); }
    function testT6() public { require(newTarget().t6() == 99, "t6"); }
    function testT7() public { require(newTarget().t7() == 42, "t7"); }
    function testT8() public { require(newTarget().t8() == 42, "t8"); }
}
