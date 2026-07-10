// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// NAMED-ARG-ORDER — regression pin for the argument-EVALUATION ORDER of an
// INTERNAL call written with NAMED arguments, against solc 0.8.35 LEGACY
// codegen (the corpus ground truth).
//
// LEGACY vs via-IR DIFFER here (verified on real EVM with Forge):
//   * solc LEGACY (optimizer off, no via-IR) evaluates the named-argument
//     expressions in the callee's PARAMETER / DECLARATION order, then binds
//     each value to its parameter by name.
//   * solc via-IR instead evaluates them in SOURCE (call-site) order.
// solidity-lean lowers an internal call's named arguments into per-parameter
// temporaries evaluated in parameter order (the `boundaryArgDecls` /
// `toExprsForParams?` path) — i.e. it ALREADY matches LEGACY.  This lane pins
// that: it guarantees the model keeps LEGACY parameter-order semantics for
// internal named arguments and does NOT drift to the via-IR source order.
//
// NOTE on scope: named-argument syntax `f({...})` is only accepted by solc for
// function calls, struct constructors, events and errors — NOT for modifier
// invocations or base-constructor calls (both rejected at parse time), so those
// kinds are unreachable.  For struct constructors / events / errors the argument
// values are assembled through the ABI/component encoder, whose child evaluation
// order is a SEPARATE, independently-tracked concern; this lane deliberately
// covers only the internal-call path, which is decoupled from that encoder.
//
// `trace` records order: each argument expression is an assignment expression
// `trace = trace * 10 + n` (side-effecting, order-observable, NOT a nested call,
// so it does not depend on any call-argument hoisting).  The final decimal
// digits encode the exact evaluation order.
contract NamedArgOrderHarnessTarget {
    uint256 public trace;

    function twoI(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * 10 + b;
    }

    function threeI(uint256 a, uint256 b, uint256 c)
        internal
        pure
        returns (uint256)
    {
        return a * 100 + b * 10 + c;
    }

    // Positional control: source order (shared by LEGACY and via-IR) => 12.
    function positionalOrder() public returns (uint256) {
        trace = 0;
        twoI(trace = trace * 10 + 1, trace = trace * 10 + 2);
        return trace;
    }

    // Internal named, 2 args. Written `{b: .. , a: ..}` (b first at call site,
    // but `a` is the first parameter). LEGACY parameter order evaluates `a`'s
    // expression first: r2 then r1 => 21. (via-IR source order would be 12.)
    function internalOrder() public returns (uint256) {
        trace = 0;
        twoI({b: trace = trace * 10 + 1, a: trace = trace * 10 + 2});
        return trace;
    }

    // Internal named, 3 args, written in the scrambled order `{c, a, b}`.
    // LEGACY parameter order (a, b, c) evaluates a's expr (r2), then b's (r3),
    // then c's (r1) => 231. (via-IR source order c,a,b would be 123.) The
    // three-way scramble makes parameter order and source order unambiguous.
    function internalThree() public returns (uint256) {
        trace = 0;
        threeI({
            c: trace = trace * 10 + 1,
            a: trace = trace * 10 + 2,
            b: trace = trace * 10 + 3
        });
        return trace;
    }
}
