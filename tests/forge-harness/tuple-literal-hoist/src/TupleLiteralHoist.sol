// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Stage-B pin for the boundary-completion arc
// (docs/refs-completion-solc-research.md §4): a tuple-literal RHS whose
// components contain internal calls. solc evaluates the components
// LEFT-to-right, each into its own temporary, ALL before any assignment;
// a hole (`(, b) = ...`) still evaluates the discarded component.
//
// The storage `log` records evaluation order (base-10 digits appended by
// each callee), and every probe encodes its observations into a single
// word so both sides assert one concrete value per entry point. Each
// probe runs against fresh state (Forge: fresh instance; Lean:
// State.empty), so `log` starts at 0.
contract TupleLiteralHoistHarnessTarget {
    uint256 private log;

    function f() internal returns (uint256) {
        log = log * 10 + 1;
        return 11;
    }

    function g() internal returns (uint256) {
        log = log * 10 + 2;
        return 22;
    }

    // (a, b) = (f(), g()) — expects a=11, b=22, log=12 (f before g).
    function assignPair() public returns (uint256) {
        uint256 a;
        uint256 b;
        (a, b) = (f(), g());
        return a * 1000000 + b * 1000 + log; // 11022012
    }

    // (, b) = (f(), g()) — the hole's component f() STILL evaluates
    // (log=12), only its store is dropped.
    function assignHole() public returns (uint256) {
        uint256 b;
        (, b) = (f(), g());
        return b * 1000 + log; // 22012
    }

    // Declaration form, reversed order: (x, y) = (g(), f()) — expects
    // x=22, y=11, log=21 (g before f).
    function declPair() public returns (uint256) {
        (uint256 x, uint256 y) = (g(), f());
        return x * 1000000 + y * 1000 + log; // 22011021
    }
}
