// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Pin for internal function-pointer equality/inequality (#50, FP-EQ).
// Internal function pointers are dispatch IDs; solc 0.8.35 legacy
// (optimizer=false) compiles `fp == g` / `fp != g` to an id/code-pointer
// comparison returning a bool. Two pointers are equal iff they refer to the
// same function (same dispatch identity). Previously solidity-lean reverted
// with Panic(0)/typeMismatch because BinaryOp.apply's eq/ne arms had no
// Value.internalFunction case. Every probe is self-contained (fresh state).
//
// NOTE: this lane covers pointers produced by DIRECT-name assignment (the
// representation the fixed arm handles). Pointers produced through a ternary
// initializer or a storage-field read are covered by the sibling lane
// `fnptr-internal-eq-derived` (#53/FP-EQ-2, docs/DECISIONS.md 2026-07-09),
// which carries the internalFunction representation through those paths.
contract FnptrInternalEqHarnessTarget {
    function a() internal pure {}
    function b() internal pure {}

    // Pointer assigned to a, compared to a: true.
    function eqSame() public pure returns (bool) {
        function() internal pure g = a;
        return g == a;
    }

    // Pointer assigned to a, compared to b: false.
    function eqDiff() public pure returns (bool) {
        function() internal pure g = a;
        return g == b;
    }

    // Pointer assigned to a, `!=` b: true.
    function neDiff() public pure returns (bool) {
        function() internal pure g = a;
        return g != b;
    }

    // Pointer assigned to a, `!=` a: false.
    function neSame() public pure returns (bool) {
        function() internal pure g = a;
        return g != a;
    }

    // Two independent pointers assigned the SAME function compare equal.
    function eqTwoSame() public pure returns (bool) {
        function() internal pure g = a;
        function() internal pure h = a;
        return g == h;
    }

    // After reassignment the pointer's identity follows the new target:
    // g starts at a (== a true), then becomes b (== a false, == b true).
    // Returns before && !afterA && afterB == true.
    function eqAfterReassign() public pure returns (bool) {
        function() internal pure g = a;
        bool before = (g == a);
        g = b;
        bool afterA = (g == a);
        bool afterB = (g == b);
        return before && !afterA && afterB;
    }
}
