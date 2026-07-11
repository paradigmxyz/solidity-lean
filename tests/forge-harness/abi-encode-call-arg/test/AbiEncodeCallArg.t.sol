// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {AbiEncodeCallArgTarget} from "../src/AbiEncodeCallArg.sol";

contract AbiEncodeCallArgForgeTest {
    function testEncReturn() public {
        AbiEncodeCallArgTarget t = new AbiEncodeCallArgTarget();
        require(abi.decode(t.encReturn(), (uint256)) == 3, "encReturn");
    }
    function testEncTwoArgs() public {
        AbiEncodeCallArgTarget t = new AbiEncodeCallArgTarget();
        (uint256 a, uint256 b) = abi.decode(t.encTwoArgs(), (uint256, uint256));
        require(a == 9, "encTwoArgs-a");
        require(b == 3, "encTwoArgs-b");
    }
    function testEncWrapper() public {
        AbiEncodeCallArgTarget t = new AbiEncodeCallArgTarget();
        require(abi.decode(t.encWrapper(), (uint256)) == 4, "encWrapper");
    }
    function testEncVarDecl() public {
        AbiEncodeCallArgTarget t = new AbiEncodeCallArgTarget();
        require(abi.decode(t.encVarDecl(), (uint256)) == 3, "encVarDecl");
    }
    function testEncDiscard() public {
        AbiEncodeCallArgTarget t = new AbiEncodeCallArgTarget();
        require(t.encDiscard() == 7, "encDiscard");
    }
}
