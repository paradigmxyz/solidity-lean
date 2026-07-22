// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {EvalOrderBinaryResidue} from "../src/EvalOrderBinaryResidue.sol";

interface VmLogs {
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }

    function recordLogs() external;

    function getRecordedLogs() external returns (Log[] memory);
}

/// Ground truth (solc 0.8.35 / Foundry EVM) for the R1 binary-order residue
/// shapes: ordinary binary operands evaluate RIGHT then LEFT even when the
/// LEFT operand is a compound expression containing its own calls, and even
/// when the RIGHT operand is pure; `emit` with two indexed args stays
/// two-phase (indexed args in reverse source order).
contract EvalOrderBinaryResidueForgeTest {
    VmLogs constant vm =
        VmLogs(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    function newC() internal returns (EvalOrderBinaryResidue) {
        return new EvalOrderBinaryResidue();
    }

    function testDirectBoth() public {
        require(newC().directBoth() == 1, "directBoth right-first");
    }

    function testLhsComplexRhsCall() public {
        require(newC().lhsComplexRhsCall() == 2, "lhsComplexRhsCall right-first");
    }

    function testIndexCallPlusCall() public {
        require(newC().indexCallPlusCall() == 31, "indexCallPlusCall right-first");
    }

    function testBothComplex() public {
        require(newC().bothComplex() == 12, "bothComplex right-first");
    }

    function testLhsCallPureRhs() public {
        require(newC().lhsCallPureRhs() == 2, "lhsCallPureRhs pure-rhs-first");
    }

    function testEmitTwoIndexed() public {
        vm.recordLogs();
        newC().emitTwoIndexed();
        VmLogs.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "one log");
        require(logs[0].topics.length == 3, "three topics");
        require(uint256(logs[0].topics[1]) == 2, "x second-evaluated = 2");
        require(uint256(logs[0].topics[2]) == 1, "y first-evaluated = 1");
    }

    function testNestedInnerDirect() public {
        require(newC().nestedInnerDirect() == 1, "nestedInnerDirect");
    }

    function testNestedInnerComplex() public {
        require(newC().nestedInnerComplex() == 1, "nestedInnerComplex");
    }
}
