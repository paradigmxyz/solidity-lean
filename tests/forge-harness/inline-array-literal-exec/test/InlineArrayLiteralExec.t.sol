// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {InlineArrayLiteralExecTarget} from "../src/InlineArrayLiteralExec.sol";

contract InlineArrayLiteralExecForgeTest {
    InlineArrayLiteralExecTarget private target =
        new InlineArrayLiteralExecTarget();

    function testVarInitNarrow() public view {
        require(target.varInitNarrow() == 10203, "uint8[3]=[1,2,3]");
    }

    function testMultidimNarrow() public view {
        require(target.multidimNarrow() == 1234, "uint8[2][2]=[[1,2],[3,4]]");
    }

    function testIndexOfLiteral() public view {
        require(target.indexOfLiteral(1) == 20, "[10,20,30][1]");
    }

    function testArgToInternal() public view {
        require(target.argToInternal() == 18, "sum3([5,6,7])");
    }

    function testReturnLiteral() public view {
        uint256[3] memory r = target.returnLiteral();
        require(r[0] == 1 && r[1] == 2 && r[2] == 3, "return [1,2,3]");
    }

    function testInt8Narrow() public view {
        require(target.int8Narrow() == 255002, "int8[2]=[int8(-1),2]");
    }
}
