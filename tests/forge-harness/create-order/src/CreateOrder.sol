// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

/// Contract-creation option/argument evaluation ORDER (gaps DIV-CREATE-1/2).
///
/// solc (v0.8.35) evaluates `new C{value: v, salt: s}(a)` as: the `{...}`
/// FunctionCallOptions in their WRITTEN (source) order FIRST, then the
/// constructor ARGUMENT LAST.  Each of the three participants appends its own
/// base-10 digit to a single storage slot via an embedded assignment
/// expression, then multiplies by zero so the option/arg value is zero (no
/// funding is needed and the create deploys for real), so the returned
/// `traceOut` spells the exact evaluation order:
///   value-first written order `{value, salt}`  ->  1 2 3
///   salt-first  written order `{salt, value}`  ->  2 1 3
/// (1 = value option, 2 = salt option, 3 = constructor arg).  This holds
/// identically for the plain `new` expression and the statement-form `try new`.
contract Target {
    constructor(uint256 a) payable {
        a;
    }
}

contract CreateOrder {
    uint256 public trace;

    // --- plain `new` expression --------------------------------------------

    function plainValueFirst() external returns (uint256 traceOut) {
        trace = 0;
        new Target{
            value: (trace = trace * 10 + 1) * 0,
            salt: bytes32((trace = trace * 10 + 2) * 0)
        }((trace = trace * 10 + 3) * 0);
        traceOut = trace;
    }

    function plainSaltFirst() external returns (uint256 traceOut) {
        trace = 0;
        new Target{
            salt: bytes32((trace = trace * 10 + 2) * 0),
            value: (trace = trace * 10 + 1) * 0
        }((trace = trace * 10 + 3) * 0);
        traceOut = trace;
    }

    // --- statement-form (try) creation -------------------------------------

    function tryValueFirst() external returns (uint256 traceOut) {
        trace = 0;
        try new Target{
            value: (trace = trace * 10 + 1) * 0,
            salt: bytes32((trace = trace * 10 + 2) * 0)
        }((trace = trace * 10 + 3) * 0) returns (Target) {} catch {}
        traceOut = trace;
    }

    function trySaltFirst() external returns (uint256 traceOut) {
        trace = 0;
        try new Target{
            salt: bytes32((trace = trace * 10 + 2) * 0),
            value: (trace = trace * 10 + 1) * 0
        }((trace = trace * 10 + 3) * 0) returns (Target) {} catch {}
        traceOut = trace;
    }
}
