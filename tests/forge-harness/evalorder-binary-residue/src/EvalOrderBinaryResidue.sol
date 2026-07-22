// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

/// R1 RESIDUE CLOSURE: binary-operand evaluation order for the two importer
/// hoister shapes that stayed LEFT-first after #187/#191 (the "Residue kept"
/// bullet in EVAL_ORDER_DESIGN.md): (a) a NON-core LHS containing its own
/// call(s) beside a call-bearing RHS (both-sides-hoisted generic path), and
/// (b) the lhs-hoisted + pure-RHS fallback. solc 0.8.35 evaluates the RIGHT
/// operand of an ordinary binary FIRST (ExpressionCompiler.cpp:614-615), so
/// with a side-effecting `bump()` the operand values are order-distinct.
/// `directBoth` (both operands direct calls) pins the already-fixed #187/#191
/// path; `emitTwoIndexed` pins the two-phase emit order (indexed args in
/// REVERSE source order) that must NOT be disturbed by the residue fix.
contract EvalOrderBinaryResidue {
    uint256 public counter;
    uint256[] private arr;

    event E2I(uint256 indexed x, uint256 indexed y);

    function bump() internal returns (uint256) {
        counter += 1;
        return counter;
    }

    // Control (fixed in R1, #187/#191): both operands direct calls.
    // RIGHT bump() = 1 first, LEFT bump() = 2 -> 2 - 1 = 1.
    function directBoth() external returns (uint256) {
        return bump() - bump();
    }

    // Residue (a): non-core LHS with a call beside a direct RHS call.
    // RIGHT bump() = 1 first, then LEFT bump() = 2, +1 = 3 -> 3 - 1 = 2.
    // (Left-first would compute (1+1) - 2 = 0.)
    function lhsComplexRhsCall() external returns (uint256) {
        return (bump() + 1) - bump();
    }

    // Residue (a), index shape: `arr[bump()] + bump()`.
    // RIGHT bump() = 1 first, then LEFT arr[bump() = 2] = 30 -> 30 + 1 = 31.
    // (Left-first would compute arr[1] + 2 = 22.)
    function indexCallPlusCall() external returns (uint256) {
        arr.push(10);
        arr.push(20);
        arr.push(30);
        return arr[bump()] + bump();
    }

    // Residue (a), generic both-sides-hoisted path: BOTH operands non-core
    // with calls. RIGHT (bump() = 1) + 3 = 4 first, then LEFT
    // (bump() = 2) + 1 = 3 -> 3 * 4 = 12. (Left-first would be 2 * 5 = 10.)
    function bothComplex() external returns (uint256) {
        return (bump() + 1) * (bump() + 3);
    }

    // Residue (b): lhs-hoisted + PURE rhs. The pure RIGHT operand (a storage
    // read) is evaluated FIRST: counter = 0, then LEFT (bump() = 1) + 1 = 2
    // -> 2 - 0 = 2. (Left-first would read counter AFTER bump: 2 - 1 = 1.)
    function lhsCallPureRhs() external returns (uint256) {
        return (bump() + 1) - counter;
    }

    // Control: emit with two INDEXED side-effecting args stays TWO-PHASE
    // (indexed args in REVERSE source order): y = bump() = 1 first, then
    // x = bump() = 2 -> topics (x = 2, y = 1).
    function emitTwoIndexed() external {
        emit E2I(bump(), bump());
    }
}
