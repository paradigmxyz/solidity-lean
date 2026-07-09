// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// DIV-CTOR-1 regression: base-constructor ARGUMENT evaluation order.
//
// `CtorArgD is CtorArgB, CtorArgC` supplies a side-effecting expression to each
// of its two base constructors via its OWN constructor-modifier list
// (`CtorArgB(r(2)) CtorArgC(r(4))`). solc (LEGACY codegen, the corpus ground
// truth) evaluates each base's supplied arguments in the supplying (most-
// derived) frame DURING the descent through the C3 linearization
// (`ContractCompiler::appendBaseConstructor` evaluates a base's args, then
// recurses into that base before running any body), and runs the constructor
// bodies base->derived.
//
// `trace` (slot 0 of `CtorArgRoot`, inherited by all) is an order-sensitive
// accumulator: `r(n)` does `trace = trace * 10 + n` and returns `n`, so the
// final digit string encodes the exact execution order.
//
// C3(CtorArgD) = [CtorArgD, CtorArgC, CtorArgB, CtorArgRoot] (solc reverses the
// direct-base list when merging). Execution order:
//   r(4): CtorArgD evaluates the arg it supplies to CtorArgC   (descent, D frame)
//   r(2): CtorArgD evaluates the arg it supplies to CtorArgB   (descent, D frame)
//   r(1): CtorArgB body
//   r(3): CtorArgC body
//   r(5): CtorArgD body
//   => trace == 42135.
//
// The pre-fix lowering assembled one piece per contract in storage order
// (base->derived) as `[block(baseArgs ++ [body])]`, evaluating each base's
// incoming args at that base's own (earlier) position rather than in the
// supplying frame during descent, giving the wrong order r(2),r(1),r(4),r(3),
// r(5) -> 21435.

contract CtorArgRoot {
    uint256 public trace;
    function r(uint256 n) internal returns (uint256) {
        trace = trace * 10 + n;
        return n;
    }
}

contract CtorArgB is CtorArgRoot {
    constructor(uint256) { r(1); }
}

contract CtorArgC is CtorArgRoot {
    constructor(uint256) { r(3); }
}

contract CtorArgD is CtorArgB, CtorArgC {
    constructor() CtorArgB(r(2)) CtorArgC(r(4)) { r(5); }
}
