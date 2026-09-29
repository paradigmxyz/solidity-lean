// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {BaseQualifiedFunctionStateVariableTarget, QualifiedDerived} from
    "../src/BaseQualifiedFunctionStateVariable.sol";

contract BaseQualifiedFunctionStateVariableTest {
    function testUnrelatedEntryStillRuns() public {
        BaseQualifiedFunctionStateVariableTarget target =
            new BaseQualifiedFunctionStateVariableTarget();
        require(target.g() == 0, "g result");
    }

    function testQualifiedZeroPointerCallPanics() public {
        BaseQualifiedFunctionStateVariableTarget target =
            new BaseQualifiedFunctionStateVariableTarget();
        (bool ok, bytes memory data) = address(target).call(
            abi.encodeCall(target.h, ())
        );
        require(!ok, "zero pointer call must fail");
        require(data.length == 36, "panic payload length");
        bytes4 selector;
        uint256 code;
        assembly {
            selector := mload(add(data, 32))
            code := mload(add(data, 36))
        }
        require(selector == 0x4e487b71, "panic selector");
        require(code == 0x51, "panic code");
    }

    function testLocalFunctionPointerDoesNotCaptureQualifiedBaseCall() public {
        QualifiedDerived target = new QualifiedDerived();
        require(target.shadowed() == 7, "base dispatch");
    }
}
