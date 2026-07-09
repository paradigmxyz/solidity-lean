// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ArrayLiteralWidenHarnessTarget} from "../src/ArrayLiteralWiden.sol";

contract ArrayLiteralWidenForgeTest {
    ArrayLiteralWidenHarnessTarget private target =
        new ArrayLiteralWidenHarnessTarget();

    function testUint8Elems() public view {
        require(target.uint8Elems() == 10203, "uint8[3]=[1,2,3]");
    }

    function testExplicit256Elems() public view {
        require(target.explicit256Elems() == 40606, "uint256[3]=[uint256(1),2,3]");
    }

    function testInt8Elems() public view {
        require(target.int8Elems() == 255002, "int8[2]=[int8(-1),2]");
    }

    function testMulti8Elems() public view {
        require(target.multi8Elems() == 1234, "uint8[2][2]=[[1,2],[3,4]]");
    }
}
