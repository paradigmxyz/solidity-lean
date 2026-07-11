// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {TupleVarDeclTernaryTarget} from "../src/TupleVarDeclTernary.sol";

contract TupleVarDeclTernaryForgeTest {
    function testPickTrue() public {
        TupleVarDeclTernaryTarget t = new TupleVarDeclTernaryTarget();
        require(t.pick(true) == 3, "pick(true)");
    }

    function testPickFalse() public {
        TupleVarDeclTernaryTarget t = new TupleVarDeclTernaryTarget();
        require(t.pick(false) == 7, "pick(false)");
    }
}
