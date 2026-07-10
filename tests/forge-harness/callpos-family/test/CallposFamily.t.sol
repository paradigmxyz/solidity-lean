// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {CallposFamilyHarnessTarget} from "../src/CallposFamily.sol";

contract CallposFamilyForgeTest {
    CallposFamilyHarnessTarget private target = new CallposFamilyHarnessTarget();

    // MULTI value — add2(gA(), hB()) = 12.
    function testMultiArgsVal() public {
        require(target.multiArgsVal() == 12, "add2(gA(), hB()) must equal 12");
    }

    // MULTI three-param, two call args — add3(gA(), 10, hB()) = 22.
    function testThreeMixedVal() public {
        require(target.threeMixedVal() == 22, "add3(gA(), 10, hB()) must equal 22");
    }

    // NESTED double — jC(jC(gA())) = 7.
    function testDoubleNestVal() public {
        require(target.doubleNestVal() == 7, "jC(jC(gA())) must equal 7");
    }

    // NESTED inside multi-arg — add2(jC(gA()), 1) = 7.
    function testNestPlusArgVal() public {
        require(target.nestPlusArgVal() == 7, "add2(jC(gA()), 1) must equal 7");
    }

    // varDecl form — uint x = add2(gA(), hB()) = 12.
    function testVarDeclMulti() public {
        require(target.varDeclMulti() == 12, "uint x = add2(gA(), hB()) must equal 12");
    }

    // eval order — multi-arg left-to-right: gA() then hB() (order trail = 12).
    function testMultiArgOrder() public {
        require(target.multiArgOrder() == 12, "gA() then hB() order must be 12");
    }

    // eval order — nested: gA(), inner jC(), outer jC() (order trail = 133).
    function testNestOrder() public {
        require(target.nestOrder() == 133, "nested order must be 133");
    }

    // control — call-free multi-argument call unchanged.
    function testControlPlain() public {
        require(target.controlPlain() == 7, "add2(3, 4) must equal 7");
    }
}
