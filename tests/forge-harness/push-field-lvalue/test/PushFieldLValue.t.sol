// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {PushFieldLValueHarnessTarget} from "../src/PushFieldLValue.sol";

contract PushFieldLValueForgeTest {
    function testStructMember() public {
        PushFieldLValueHarnessTarget t = new PushFieldLValueHarnessTarget();
        (uint256 len, uint256 a0, uint256 b0) = t.structMember();
        require(len == 1, "len");
        require(a0 == 7, "a0");
        require(b0 == 0, "b0");
    }

    function testStructTwoFields() public {
        PushFieldLValueHarnessTarget t = new PushFieldLValueHarnessTarget();
        (uint256 len, uint256 a0, uint256 b0, uint256 a1, uint256 b1) = t.structTwoFields();
        require(len == 2, "len");
        require(a0 == 7, "a0");
        require(b0 == 0, "b0");
        require(a1 == 0, "a1");
        require(b1 == 9, "b1");
    }

    function testArrayIndex() public {
        PushFieldLValueHarnessTarget t = new PushFieldLValueHarnessTarget();
        (uint256 len, uint256 e0, uint256 e1, uint256 e2) = t.arrayIndex();
        require(len == 1, "len");
        require(e0 == 0, "e0");
        require(e1 == 9, "e1");
        require(e2 == 0, "e2");
    }
}
