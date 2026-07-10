// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// G#116 (TERNARY-STORAGE-STATELVALUE) — solc ACCEPTS a `storage`-pointer local
// initialized from a TERNARY of two storage state variables:
//   `S storage p = b ? s0 : s1;`
// TypeChecker::visit(VariableDeclarationStatement) gates a storage-pointer
// local only on `isImplicitlyConvertibleTo` (no lvalue requirement); a
// conditional of two storage references (TypeChecker::visit(Conditional) takes
// the common type of the branches) is itself a storage reference implicitly
// convertible to `S storage`. solidity-lean formerly over-rejected this because
// the ternary CheckedExpr builder dropped the `stateLValue` marker.
//
// The pointer must ALIAS the SELECTED state variable: writing through `p`
// mutates exactly `b ? s0 : s1` and leaves the other slot untouched. This lane
// pins that aliasing on real EVM (Forge) and re-checks it on the Lean side from
// the imported solc AST.
contract TernaryStoragePointerHarnessTarget {
    struct S {
        uint x;
    }

    S s0;
    S s1;

    // Write `v` through the ternary-selected storage pointer, then return the
    // SELECTED state var — it must equal `v` (the write went to `b ? s0 : s1`).
    function aliasSelected(bool b, uint v) external returns (uint) {
        S storage p = b ? s0 : s1;
        p.x = v;
        return b ? s0.x : s1.x;
    }

    // Same write; return the OTHER state var — it must stay 0 (the write did
    // not leak into the unselected slot).
    function otherUntouched(bool b, uint v) external returns (uint) {
        S storage p = b ? s0 : s1;
        p.x = v;
        return b ? s1.x : s0.x;
    }

    // The bare #116 repro: read through the ternary storage pointer.
    function readThrough(bool b) external view returns (uint) {
        S storage p = b ? s0 : s1;
        return p.x;
    }

    // A ternary storage reference passed to a `storage`-ref parameter.
    function readParam(S storage r) internal view returns (uint) {
        return r.x;
    }

    function passToStorageParam(bool b) external view returns (uint) {
        return readParam(b ? s0 : s1);
    }

    // Direct getters so the Forge test can independently observe raw slots.
    function getS0() external view returns (uint) {
        return s0.x;
    }

    function getS1() external view returns (uint) {
        return s1.x;
    }
}
