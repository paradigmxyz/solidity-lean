// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// R1 — a NESTED tuple on the assignment LHS whose RHS contains INTERNAL
// function calls. solc accepts both shapes; the RHS is evaluated once,
// left-to-right, into temps (side effects observed in that order) and then
// destructured against the nested target tree. Solidus formerly over-rejected
// these (the nested elaboration could not hoist internal calls out of the RHS).
contract NestedTupleInternalCallHarnessTarget {
    uint256 order;

    // A multi-return internal call filling a nested target, plus a scalar call.
    function foo() internal returns (uint256, uint256) { order = order * 10 + 1; return (10, 20); }
    function bar() internal returns (uint256) { order = order * 10 + 2; return 30; }

    // ((a, b), c) = (foo(), bar()) — foo()'s 2-tuple destructures into (a, b).
    // order == 12 proves foo() ran before bar() (left-to-right, temps first).
    function flatMulti() external returns (uint256) {
        uint256 a; uint256 b; uint256 c;
        ((a, b), c) = (foo(), bar());
        return a * 1000000 + b * 10000 + c * 100 + order;
    }

    // Scalar internal calls in nested RHS positions.
    function g() internal returns (uint256) { order = order * 10 + 3; return 100; }
    function h() internal returns (uint256) { order = order * 10 + 4; return 200; }
    function k() internal returns (uint256) { order = order * 10 + 5; return 300; }

    // ((a, b), c) = ((g(), h()), k()) — order == 345 (g, h, k left-to-right).
    function nestedCalls() external returns (uint256) {
        uint256 a; uint256 b; uint256 c;
        ((a, b), c) = ((g(), h()), k());
        return a * 1000000 + b * 10000 + c * 100 + order;
    }

    // A hole in a nested position still evaluates its component call (side
    // effect happens) but discards the value.
    function p() internal returns (uint256) { order = order * 10 + 6; return 400; }
    function q() internal returns (uint256) { order = order * 10 + 7; return 500; }
    function nestedHole() external returns (uint256) {
        uint256 a; uint256 c;
        ((a, ), c) = ((p(), q()), 999);
        return a * 10000 + c * 100 + order;
    }
}
