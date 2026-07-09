// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

/// External-call argument/option evaluation ORDER (gap EO1).
///
/// solc (v0.8.35) evaluates `base.f{gas: g(), value: v()}(payload)` as: the
/// base/target expression FIRST, then the call options in their WRITTEN order
/// (gas-vs-value governed by which option is written first), then the calldata
/// argument LAST.  Each of the four participants appends its own base-10 digit
/// to a single storage slot via an embedded assignment expression, so the
/// returned `traceOut` spells the exact evaluation order:
///   gas-first  written order `{gas, value}`   ->  1 2 3 4
///   value-first written order `{value, gas}`   ->  1 3 2 4
/// (1 = target, 2 = gas, 3 = value, 4 = calldata).  This holds identically for
/// the expression-form low-level `.call` and the statement-form `try` call.
interface IOrderCallee {
    function sink(bytes calldata payload) external payable returns (uint256);
}

contract CallOptionEvalOrder {
    uint256 public trace;

    // --- expression-form low-level `.call` ---------------------------------

    function exprGasFirst() external returns (uint256 traceOut) {
        trace = 0;
        (bool ok, ) = address(uint160(trace = trace * 10 + 1)).call{
            gas: (trace = trace * 10 + 2),
            value: (trace = trace * 10 + 3)
        }(abi.encodePacked(uint8(trace = trace * 10 + 4)));
        ok;
        traceOut = trace;
    }

    function exprValueFirst() external returns (uint256 traceOut) {
        trace = 0;
        (bool ok, ) = address(uint160(trace = trace * 10 + 1)).call{
            value: (trace = trace * 10 + 3),
            gas: (trace = trace * 10 + 2)
        }(abi.encodePacked(uint8(trace = trace * 10 + 4)));
        ok;
        traceOut = trace;
    }

    // --- statement-form (try) external call --------------------------------

    function tryGasFirst() external returns (uint256 traceOut) {
        trace = 0;
        try
            IOrderCallee(address(uint160(trace = trace * 10 + 1))).sink{
                gas: (trace = trace * 10 + 2),
                value: (trace = trace * 10 + 3)
            }(abi.encodePacked(uint8(trace = trace * 10 + 4)))
        returns (uint256) {} catch {}
        traceOut = trace;
    }

    function tryValueFirst() external returns (uint256 traceOut) {
        trace = 0;
        try
            IOrderCallee(address(uint160(trace = trace * 10 + 1))).sink{
                value: (trace = trace * 10 + 3),
                gas: (trace = trace * 10 + 2)
            }(abi.encodePacked(uint8(trace = trace * 10 + 4)))
        returns (uint256) {} catch {}
        traceOut = trace;
    }
}
