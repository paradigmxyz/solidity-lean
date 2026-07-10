// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// OVERREJECT-CALLPOS-BATCH — a batch of confirmed over-rejects in the
// call-position lowering family. A user CALL is a STATEMENT in the Executable
// core, so a call nested in a sub-expression must be HOISTED into a prefix
// temp-binding. solc 0.8.35 legacy ACCEPTS + compiles each of these; the model
// used to return `none` (reject the whole contract) at Source->Executable.
//
//   A. `T x = outer(inner())` — a direct internal call whose ARGUMENT is itself
//      a direct internal call. The single-binding varDecl arm never hoisted the
//      nested-call argument. Fix: mirror the statement/multi-binding arms and
//      hoist the argument call into a prefix temp, then lower the outer call
//      against the temp. solc evaluates the inner call first, then the outer
//      (verified via `--ir`): `inner()` before `outer(expr)`.
//
//   B. `T x = m[f()]` / `y = m[f()]` / `T z = m[f()] + 1` — an internal call
//      used as a mapping/array INDEX in a NON-return read position. The index
//      call was only hoisted in the return arm. Fix: add an `Expr.index base
//      (call)` arm to the single-return expression hoister (reusing the return
//      arm's `indexReadCoreBuilder?`), and route the generic varDecl / plain
//      assign fallbacks through that hoister. The base is a pure reference (no
//      eval side effect), so hoisting the index call preserves solc order.
//
//   E. `m[f()] = g()` — an index-ASSIGN whose target index AND right-hand side
//      are both calls. The existing index-assign hoist lowered the RHS purely,
//      failing for a call RHS. Fix: on pure-RHS failure, declare the RHS temp
//      uninitialised, hoist the RHS call into it, THEN hoist the index call —
//      preserving solc's RHS-before-index order (verified via `--ir`: `m[f()] =
//      g()` runs g() before f()).
//
// Everything here is own-call executable (internal calls + mappings + state
// vars), so acceptance AND runtime are pinned by own-contract execution; the
// eval-order pins (`orderCompose`, `writeIdxOrder`) are correct only if the
// hoisted calls run in solc's order. Call-free controls pin the pre-existing
// pure paths. The Forge test re-checks every case against real solc/EVM.
contract OverrejectCallposBatchHarnessTarget {
    mapping(uint256 => uint256) private mp;
    uint256 private ord;

    // inner()/outer(a): an inner call feeding an outer call's argument. Each
    // records its evaluation into `ord` (base-10 digit trail) so the composed
    // order is observable.
    function inner() internal returns (uint256) {
        ord = ord * 10 + 1;
        return 3;
    }

    function outer(uint256 a) internal returns (uint256) {
        ord = ord * 10 + 2;
        return a + 100;
    }

    // f(): an internal call producing a mapping index (records order digit 1).
    function f() internal returns (uint256) {
        ord = ord * 10 + 1;
        return 2;
    }

    // gval(): an internal call producing an assignment RHS value (order digit 2).
    function gval() internal returns (uint256) {
        ord = ord * 10 + 2;
        return 77;
    }

    // A — value pin: inner() = 3, outer(3) = 103.
    function composeVal() external returns (uint256) {
        uint256 x = outer(inner());
        return x;
    }

    // A — eval-order pin: inner() runs first (ord = 1), then outer() (ord = 12).
    // A read-before / swapped order would give 21.
    function orderCompose() external returns (uint256) {
        ord = 0;
        uint256 x = outer(inner());
        // `x` (= 103) must be the composed value; return the order trail.
        if (x == 103) {
            return ord;
        }
        return 999;
    }

    // B — varDecl index read: mp[f()] with f() = 2 reads mp[2] = 55.
    function readIdx() external returns (uint256) {
        mp[2] = 55;
        uint256 x = mp[f()];
        return x;
    }

    // B — plain-assign index read: y = mp[f()] reads mp[2] = 66.
    function assignIdx() external returns (uint256) {
        mp[2] = 66;
        uint256 y;
        y = mp[f()];
        return y;
    }

    // B — index read inside a binary operand: mp[f()] + 1 = 55 + 1 = 56.
    function binIdx() external returns (uint256) {
        mp[2] = 55;
        uint256 z = mp[f()] + 1;
        return z;
    }

    // E — index-assign with a call RHS: mp[f()] = gval() writes 77 to mp[2].
    function writeIdx() external returns (uint256) {
        mp[2] = 0;
        mp[f()] = gval();
        return mp[2];
    }

    // E — eval-order pin: solc runs gval() first (ord = 2), then f() (ord = 21).
    // An index-before-RHS order would give 12.
    function writeIdxOrder() external returns (uint256) {
        ord = 0;
        mp[f()] = gval();
        return ord;
    }

    // Control — call-free varDecl unchanged.
    function plainVarDeclControl() external pure returns (uint256) {
        uint256 x = 5;
        return x;
    }

    // Control — call-free index read unchanged.
    function plainIdxControl() external returns (uint256) {
        mp[3] = 9;
        uint256 x = mp[3];
        return x;
    }

    // Control — call-free index assign unchanged.
    function plainWriteControl() external returns (uint256) {
        mp[4] = 0;
        mp[4] = 88;
        return mp[4];
    }
}
