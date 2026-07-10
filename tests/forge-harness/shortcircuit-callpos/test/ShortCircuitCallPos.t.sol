// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ShortCircuitCallPosTarget} from "../src/ShortCircuitCallPos.sol";

// Real solc/EVM ground truth for #131 SHORTCIRCUIT-CALL-POS. Each test uses a
// FRESH target so the `_counter` side-effect witness is isolated: a counter that
// stays 0 after a `*Short` call proves the effectful skipped operand did NOT run
// (short-circuit); its `*Run` twin selects that operand and leaves counter 1.
contract ShortCircuitCallPosForgeTest {
    // --- Case 1: BOTH-EXTERNAL && / || ---
    function testBothAndShort() public {
        ShortCircuitCallPosTarget t = new ShortCircuitCallPosTarget();
        require(t.bothAndShort() == false, "bothAndShort value");
        require(t.counter() == 0, "bothAndShort short-circuit: rhs skipped");
    }

    function testBothAndRun() public {
        ShortCircuitCallPosTarget t = new ShortCircuitCallPosTarget();
        require(t.bothAndRun() == true, "bothAndRun value");
        require(t.counter() == 1, "bothAndRun: rhs ran");
    }

    function testBothOrShort() public {
        ShortCircuitCallPosTarget t = new ShortCircuitCallPosTarget();
        require(t.bothOrShort() == true, "bothOrShort value");
        require(t.counter() == 0, "bothOrShort short-circuit: rhs skipped");
    }

    function testBothOrRun() public {
        ShortCircuitCallPosTarget t = new ShortCircuitCallPosTarget();
        require(t.bothOrRun() == true, "bothOrRun value");
        require(t.counter() == 1, "bothOrRun: rhs ran");
    }

    function testChainAnd() public {
        ShortCircuitCallPosTarget t = new ShortCircuitCallPosTarget();
        require(t.chainAnd() == true, "chainAnd value");
    }

    // --- Case 2: EXTERNAL ternary CONDITION ---
    function testExtTernaryTrue() public {
        ShortCircuitCallPosTarget t = new ShortCircuitCallPosTarget();
        require(t.extTernaryTrue() == 1, "extTernaryTrue value");
    }

    function testExtTernaryFalse() public {
        ShortCircuitCallPosTarget t = new ShortCircuitCallPosTarget();
        require(t.extTernaryFalse() == 2, "extTernaryFalse value");
    }

    // --- Case 3: CALL-IN-PURE-OPERAND ---
    function testCallInPure() public {
        ShortCircuitCallPosTarget t = new ShortCircuitCallPosTarget();
        require(t.callInPure() == true, "callInPure value");
    }

    function testCallInPureShort() public {
        ShortCircuitCallPosTarget t = new ShortCircuitCallPosTarget();
        require(t.callInPureShort() == false, "callInPureShort value");
        require(t.counter() == 0, "callInPureShort short-circuit: inner call skipped");
    }

    function testCallInPureRun() public {
        ShortCircuitCallPosTarget t = new ShortCircuitCallPosTarget();
        require(t.callInPureRun() == true, "callInPureRun value");
        require(t.counter() == 1, "callInPureRun: inner call ran");
    }
}
