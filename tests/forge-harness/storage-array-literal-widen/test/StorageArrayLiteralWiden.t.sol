// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {StorageArrayLiteralWidenHarnessTarget} from "../src/StorageArrayLiteralWiden.sol";

contract StorageArrayLiteralWidenForgeTest {
    StorageArrayLiteralWidenHarnessTarget private target =
        new StorageArrayLiteralWidenHarnessTarget();

    function testRun() public view {
        (uint256 x0, uint256 x1) = target.run();
        require(x0 == 50 && x1 == 0, "uint256[2]=[50,0]");
    }

    function testA0() public view {
        require(target.a0() == 50, "arr[0]");
    }

    function testA1() public view {
        require(target.a1() == 0, "arr[1]");
    }

    function testWide16() public view {
        require(target.wide16Sum() == 10203, "uint16[3]=[1,2,3]");
    }

    function testNested() public view {
        require(target.nestedSum() == 1234, "uint256[2][2]=[[1,2],[3,4]]");
    }

    function testTypedLead() public view {
        require(target.typedLeadSum() == 9007, "uint256[2]=[uint8(9),7]");
    }
}
