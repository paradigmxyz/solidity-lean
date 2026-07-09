// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {CallOptionEvalOrder} from "../src/CallOptionEvalOrder.sol";

/// Ground-truth (solc 0.8.35 / Foundry EVM) for external-call option/argument
/// evaluation order (gap EO1): target -> options(written order) -> calldata,
/// yielding order-trace 1234 for `{gas, value}` and 1324 for `{value, gas}`,
/// identically for the expression `.call` and statement `try` forms.
contract CallOptionEvalOrderForgeTest {
    function testExprGasFirst() public {
        CallOptionEvalOrder c = new CallOptionEvalOrder();
        require(c.exprGasFirst() == 1234, "expr {gas,value}");
    }

    function testExprValueFirst() public {
        CallOptionEvalOrder c = new CallOptionEvalOrder();
        require(c.exprValueFirst() == 1324, "expr {value,gas}");
    }

    function testTryGasFirst() public {
        CallOptionEvalOrder c = new CallOptionEvalOrder();
        require(c.tryGasFirst() == 1234, "try {gas,value}");
    }

    function testTryValueFirst() public {
        CallOptionEvalOrder c = new CallOptionEvalOrder();
        require(c.tryValueFirst() == 1324, "try {value,gas}");
    }
}
