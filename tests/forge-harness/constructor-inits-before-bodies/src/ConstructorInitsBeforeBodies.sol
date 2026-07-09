// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// DIV-CTOR-2 regression: inline state-variable initializers across the WHOLE
// hierarchy run BEFORE any constructor body under LEGACY codegen (the corpus
// ground truth). `ContractCompiler::appendInitAndConstructorCode` runs
// `initializeStateVariables` for every contract (base->derived) before it runs
// any constructor body.
//
// `CtorInitBase`'s constructor sets `trace = 7`. `CtorInitD` has an inline
// initializer `observed = trace` that reads the inherited `trace`.
//
// Legacy order: all inline initializers first (whole hierarchy), so
// `observed = trace` reads trace == 0 (the base body has NOT run yet) -> the
// deployed contract has observed == 0 and trace == 7.
//
// The --via-ir / pre-fix lowering instead runs each contract's initializer
// immediately before its own body (after the base ctor body), so
// `observed = trace` would read 7. Reading `observed` therefore distinguishes
// the two lowerings; the LEGACY corpus requires observed == 0.

contract CtorInitBase {
    uint256 public trace;
    constructor() { trace = 7; }
}

contract CtorInitD is CtorInitBase {
    uint256 public observed = trace;
    constructor() {}
}
