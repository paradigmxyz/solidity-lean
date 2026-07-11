// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// TUPLE-VARDECL-TERNARY (#172) — a multi-binding tuple variable DECLARATION whose
// initializer is a ternary of tuples: `(uint a, uint b) = c ? (1, 2) : (3, 4)`.
// solc accepts this (the tuple-typed ternary is destructured into the declared
// locals); solidity-lean accepted the contract but the source→core lowering
// handled the tuple-decl RHS only in the literal-`Expr.tuple` / CALL-shaped
// forms, so the ternary RHS in DECLARATION position was missed and replay
// yielded `TypeError.unsupported`. Same root/fix as #171 (abi.decode RHS): the
// declaration lowering now routes ANY tuple-typed RHS through the shared
// tuple-ASSIGNMENT machinery (declare locals, then `assignTuple`).
contract TupleVarDeclTernaryTarget {
    function pick(bool c) external pure returns (uint256) {
        (uint256 a, uint256 b) = c ? (uint256(1), uint256(2)) : (uint256(3), uint256(4));
        return a + b; // c ? 3 : 7
    }
}
