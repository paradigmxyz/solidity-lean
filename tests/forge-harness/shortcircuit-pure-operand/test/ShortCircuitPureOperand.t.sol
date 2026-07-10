// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ShortCircuitPureOperandTarget} from "../src/ShortCircuitPureOperand.sol";

// Real solc/EVM ground truth for #131 case 3 (call-in-pure-operand), matching the
// in-model semantics eval: the skipped operand's effect/Panic does NOT execute,
// the selected operand's Panic DOES.
contract ShortCircuitPureOperandForgeTest {
    function testPureOperand() public {
        ShortCircuitPureOperandTarget t = new ShortCircuitPureOperandTarget();
        require(t.pureOperand() == true, "pureOperand value");
    }

    function testSkipEffect() public {
        ShortCircuitPureOperandTarget t = new ShortCircuitPureOperandTarget();
        require(t.skipEffect() == false, "skipEffect value");
        require(t.counter() == 0, "skipEffect short-circuit: inner call skipped");
    }

    function testRunEffect() public {
        ShortCircuitPureOperandTarget t = new ShortCircuitPureOperandTarget();
        require(t.runEffect() == true, "runEffect value");
        require(t.counter() == 1, "runEffect: inner call ran");
    }

    function testSkipPanic() public {
        ShortCircuitPureOperandTarget t = new ShortCircuitPureOperandTarget();
        require(t.skipPanic() == false, "skipPanic short-circuit: no panic");
    }

    function testSkipPanicOr() public {
        ShortCircuitPureOperandTarget t = new ShortCircuitPureOperandTarget();
        require(t.skipPanicOr() == true, "skipPanicOr short-circuit: no panic");
    }

    function testRunPanicReverts() public {
        ShortCircuitPureOperandTarget t = new ShortCircuitPureOperandTarget();
        try t.runPanic() returns (bool) {
            require(false, "runPanic should revert (div by zero)");
        } catch {}
    }
}
