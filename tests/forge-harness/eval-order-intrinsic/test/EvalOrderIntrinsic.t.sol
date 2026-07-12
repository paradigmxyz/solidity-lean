// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {EvalOrderIntrinsic, EvalOrderInlineArray} from "../src/EvalOrderIntrinsic.sol";

interface VmLogs {
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }

    function recordLogs() external;

    function getRecordedLogs() external returns (Log[] memory);
}

/// Ground-truth (solc 0.8.35 / Foundry EVM) for sibling-expression evaluation
/// order: argument/tuple/array/abi/custom-error/index lists run LEFT to RIGHT;
/// binary operands and assignment RHS-vs-LHS-ref stay RIGHT-first; `emit` is
/// TWO-PHASE (indexed args in reverse source order, then data args forward).
contract EvalOrderIntrinsicForgeTest {
    VmLogs constant vm =
        VmLogs(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    function newC() internal returns (EvalOrderIntrinsic) {
        return new EvalOrderIntrinsic();
    }

    function testTupleRhs() public {
        (uint256 a, uint256 b) = newC().tupleRhs();
        require(a == 0 && b == 1, "tupleRhs");
    }

    function testReturnTuple() public {
        (uint256 a, uint256 b) = newC().returnTuple();
        require(a == 0 && b == 1, "returnTuple");
    }

    function testCallArgs() public {
        require(newC().callArgs() == 12, "callArgs 012");
    }

    function testAbiEnc() public {
        bytes memory got = newC().abiEnc();
        require(
            keccak256(got) == keccak256(abi.encode(uint256(0), uint256(1))),
            "abiEnc"
        );
    }

    function testInlineArray() public {
        (uint256 a, uint256 b, uint256 c) =
            new EvalOrderInlineArray().inlineArray();
        require(a == 0 && b == 1 && c == 2, "inlineArray");
    }

    function testIndexLhs() public {
        require(newC().indexLhs() == 99, "indexLhs m[0][1]");
    }

    function testRevertErr() public {
        EvalOrderIntrinsic c = newC();
        try c.revertErr() {
            revert("should revert");
        } catch (bytes memory data) {
            require(
                keccak256(data) ==
                    keccak256(
                        abi.encodeWithSelector(
                            EvalOrderIntrinsic.Err.selector,
                            uint256(0),
                            uint256(1)
                        )
                    ),
                "revertErr Err(0,1)"
            );
        }
    }

    function testEmitAllData() public {
        EvalOrderIntrinsic c = newC();
        vm.recordLogs();
        c.emitAllData();
        VmLogs.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "one log");
        require(logs[0].topics.length == 1, "topic0 only");
        (uint256 a, uint256 b, uint256 d) =
            abi.decode(logs[0].data, (uint256, uint256, uint256));
        require(a == 0 && b == 1 && d == 2, "AllData(0,1,2)");
    }

    function testEmitMixedTwoPhase() public {
        EvalOrderIntrinsic c = newC();
        vm.recordLogs();
        c.emitMixed();
        VmLogs.Log[] memory logs = vm.getRecordedLogs();
        require(logs.length == 1, "one log");
        require(logs[0].topics.length == 3, "topic0 + 2 indexed");
        // Indexed args evaluated in REVERSE source order first: c=0, a=1.
        require(uint256(logs[0].topics[1]) == 1, "topic a == 1");
        require(uint256(logs[0].topics[2]) == 0, "topic c == 0");
        // Then data args forward: b=2, d=3.
        (uint256 b, uint256 d) =
            abi.decode(logs[0].data, (uint256, uint256));
        require(b == 2 && d == 3, "data (2,3)");
    }

    function testBinaryOrder() public {
        require(newC().binaryOrder() == 5, "binary right-then-left");
    }

    function testArrAssign() public {
        (uint256 a0, uint256 a1, uint256 a2, uint256 iOut) =
            newC().arrAssign();
        require(a0 == 7 && a1 == 0 && a2 == 7 && iOut == 2, "arrAssign");
    }

    function testArrCompound() public {
        (uint256 a0, uint256 a1, uint256 a2, uint256 iOut) =
            newC().arrCompound();
        require(a0 == 7 && a1 == 7 && a2 == 7 && iOut == 2, "arrCompound");
    }

    function testShortCircuit() public {
        require(newC().scAnd() == 1, "scAnd");
        require(newC().scOr() == 1001, "scOr");
    }

    function testDataDep() public {
        (uint256 a, uint256 b) = newC().dataDep();
        require(a == 5 && b == 6, "dataDep");
    }
}
