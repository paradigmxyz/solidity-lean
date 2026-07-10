// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CALLPOS-FAMILY — the remaining still-reachable call-position over-rejects
// after the boundary-completion arc. A user CALL is a STATEMENT in the
// Executable core, so a call nested in a sub-expression must be HOISTED into a
// prefix temp-binding. The earlier single-argument hoist peeled only the FIRST
// direct-call argument, so two idioms kept over-rejecting (solc 0.8.35 legacy
// ACCEPTS + compiles each; the model returned `none` at Source->Executable):
//
//   * MULTIPLE call arguments in one call — `f(g(), h())`, `f(g(), 10, h())`.
//     A second call argument left `replacedArgs` still unlowerable.
//   * NESTED call arguments — `f(g(h()))`, `f(f(g()))`, `f(g(h()), 1)`. The
//     hoisted argument call was itself lowered through the pure per-arg path,
//     which cannot lower ITS call argument.
//
// Fix: `FunctionDecl.hoistDirectInternalCallArgs?` hoists EVERY direct-call
// argument (nested-first, then left-to-right) into ordered prefix temps, wired
// into the call-statement / return / single- and multi-binding varDecl arms.
// solc legacy evaluates call arguments left-to-right and a nested call before
// the call that consumes it (verified via `--ir`); the prefix reproduces that.
//
// Everything here is own-call executable (internal calls + a state var), so
// acceptance AND runtime are pinned by own-contract execution — the eval-order
// pins (`multiArgOrder`, `nestOrder`) are correct only if the hoisted calls run
// in solc's order. Call-free controls pin the pre-existing pure path. The Forge
// test re-checks every case against real solc/EVM.
contract CallposFamilyHarnessTarget {
    // Base-10 digit trail recording the evaluation order of the helpers below.
    uint256 private ord;

    // gA()/hB(): leaf calls that record their evaluation (digits 1 and 2) and
    // return distinct constants.
    function gA() internal returns (uint256) {
        ord = ord * 10 + 1;
        return 5;
    }

    function hB() internal returns (uint256) {
        ord = ord * 10 + 2;
        return 7;
    }

    // jC(a): a one-argument call that records its evaluation (digit 3); used to
    // build nested-call arguments.
    function jC(uint256 a) internal returns (uint256) {
        ord = ord * 10 + 3;
        return a + 1;
    }

    // Pure combiners (no side effect / no nested call of their own).
    function add2(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }

    function add3(uint256 a, uint256 b, uint256 c) internal pure returns (uint256) {
        return a + b + c;
    }

    // MULTI (value) — two direct-call arguments in one call: add2(5, 7) = 12.
    function multiArgsVal() external returns (uint256) {
        return add2(gA(), hB());
    }

    // MULTI (three params, two call args) — add3(5, 10, 7) = 22.
    function threeMixedVal() external returns (uint256) {
        return add3(gA(), 10, hB());
    }

    // NESTED (double) — jC(jC(gA())): gA()=5, jC(5)=6, jC(6)=7.
    function doubleNestVal() external returns (uint256) {
        return jC(jC(gA()));
    }

    // NESTED inside a multi-arg call — add2(jC(gA()), 1): jC(5)=6, 6+1 = 7.
    function nestPlusArgVal() external returns (uint256) {
        return add2(jC(gA()), 1);
    }

    // Value via a single-binding varDecl (exercises the varDecl arm): 12.
    function varDeclMulti() external returns (uint256) {
        uint256 x = add2(gA(), hB());
        return x;
    }

    // Value discarded via a call STATEMENT arm, order observed afterwards.
    // solc evaluates arguments left-to-right: gA() (ord=1) then hB() (ord=12).
    // A swapped order would give 21.
    function multiArgOrder() external returns (uint256) {
        ord = 0;
        add2(gA(), hB());
        return ord;
    }

    // Nested-call eval order: innermost gA() (ord=1), inner jC() (ord=13),
    // outer jC() (ord=133). A different peel order would not give 133.
    function nestOrder() external returns (uint256) {
        ord = 0;
        jC(jC(gA()));
        return ord;
    }

    // Control — call-free multi-argument call unchanged: add2(3, 4) = 7.
    function controlPlain() external pure returns (uint256) {
        return add2(3, 4);
    }
}
