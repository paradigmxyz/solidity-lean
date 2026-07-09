// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Pin for internal function-pointer equality/inequality on pointers PRODUCED
// through a ternary initializer or a STORAGE-field read (#53, FP-EQ-2 —
// follow-up to #50 FP-EQ / the fnptr-internal-eq lane, which covers only
// direct-name assignment).
//
// Internal function pointers are dispatch IDs; solc 0.8.35 legacy
// (optimizer=false) compiles `fp == g` / `fp != g` to an id/code-pointer
// comparison returning a bool regardless of how `fp` was produced. Two
// pointers are equal iff they refer to the same function (same dispatch
// identity). Previously solidity-lean lowered a ternary/storage-derived
// pointer to a plain `Value.word`, so it reverted/mis-typed on comparison
// (`internalFunction == word` -> typeMismatch). The FP-EQ-2 fix carries the
// `Value.internalFunction` representation through every typed lowering
// context. Every probe is self-contained (fresh state).
contract FnptrInternalEqDerivedHarnessTarget {
    function a() internal pure {}
    function b() internal pure {}

    function() internal pure sfp;

    // Ternary-initialized pointer, compared by identity to `a`.
    // p ? a : b, then `== a`  ==>  returns p.
    function ternEq(bool p) public pure returns (bool) {
        function() internal pure fp = p ? a : b;
        return fp == a;
    }

    // Ternary-initialized pointer, `!=` a  ==>  returns !p.
    function ternNe(bool p) public pure returns (bool) {
        function() internal pure fp = p ? a : b;
        return fp != a;
    }

    // Storage round-trip: write `a`, read it back, compare to `a`: true.
    function storeThenEqSame() public returns (bool) {
        sfp = a;
        return sfp == a;
    }

    // Storage round-trip: write `a`, read it back, compare to `b`: false.
    function storeThenEqDiff() public returns (bool) {
        sfp = a;
        return sfp == b;
    }

    // Storage round-trip with `!=`: write `b`, read it back, `!= a`: true.
    function storeThenNe() public returns (bool) {
        sfp = b;
        return sfp != a;
    }
}
