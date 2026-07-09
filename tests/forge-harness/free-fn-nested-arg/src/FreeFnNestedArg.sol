// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// FREE-ARG — a FREE (file-level) function call nested in the ARGUMENT position
// of another call. solc accepts and runs these (ordinary Solidity);
// solidity-lean formerly over-rejected the WHOLE contract at Executable
// lowering because `FunctionDecl.directOrPtrCallArgReturnTy?` — the return-type
// gate that guards the nested-argument hoist — took only the contract-member
// `functions` list and dropped `freeFunctions`, so a nested free callee's
// return type resolved to `none` and lowering fell through to the unsupported
// reject. The fix threads `freeFunctions` into that gate (mirroring the sibling
// helpers `internalCalleeReturnTys?` / `abiTyWithInternalFunctionsEnv?`), so the
// nested free call hoists into a temp exactly like a nested member call already
// did. A nested MEMBER call in the same position always worked, so this lane
// pairs the free case against a member-enclosed case to pin the distinction.
//
// This lane exercises the fixed positions: the return statement (both a free
// and a member enclosing call), a struct-passing return, and an expression
// statement (all three threaded call sites except varDecl-init).
//
// SCOPED OUT (two separate, pre-existing gaps, each affecting MEMBER calls
// identically, so orthogonal to the free-function threading fix):
//   1. varDecl initializer: `uint y = outer(inner(x));`. The varDecl-init
//      nested-arg arm lowers via internalVarDeclAssignReturnCallCorePieces?,
//      which requires a STORAGE-ref return and returns none for a plain-value
//      enclosing call — so even `uint y = member(memberInner(x))` (all member)
//      over-rejects. Deferred to a plain-value varDecl-init lowering.
//   2. DOUBLE-nested calls such as outer(inner(inner(x))): the single-level
//      hoist peels only the outer argument and cannot lower that peeled call's
//      OWN internal-call argument (Parameter.toStorageAwareCoreArgDecl? has no
//      internal-call fallback). Deferred to a recursive-hoist change.

function inner(uint256 a) pure returns (uint256) { return a * 2; }
function outer(uint256 a) pure returns (uint256) { return a + 1; }
function sink(uint256 a) pure returns (uint256) { return a + 1; }

struct P { uint256 x; uint256 y; }
function mk(uint256 a, uint256 b) pure returns (P memory) { return P(a, b); }
function sum(P memory p) pure returns (uint256) { return p.x + p.y; }

contract FreeFnNestedArgHarnessTarget {
    uint256 public s;

    // FREE outer, FREE inner nested in outer's arg position: outer(inner(x)).
    // run(5): inner(5) = 10, outer(10) = 11.
    function run(uint256 x) external pure returns (uint256) {
        return outer(inner(x));
    }

    // Contract MEMBER `member`, with a FREE `inner` nested in its arg position:
    // member(inner(x)). runMember(5): inner(5) = 10, member(10) = 110.
    function member(uint256 a) public pure returns (uint256) { return a + 100; }
    function runMember(uint256 x) external pure returns (uint256) {
        return member(inner(x));
    }

    // Struct-passing: a FREE `mk` (returns a memory struct) nested in the arg
    // position of a FREE `sum`. runStruct(): mk(1,2) = P(1,2), sum = 3.
    function runStruct() external pure returns (uint256) {
        return sum(mk(1, 2));
    }

    // Nested FREE call in the arg position of a bare EXPRESSION STATEMENT
    // (result discarded): `sink(inner(x));`. The statement must lower without
    // rejecting the contract; the observable is the subsequent state write.
    // runExprStmt(5): sink(inner(5)) evaluated and discarded, then s = 7.
    function runExprStmt(uint256 x) external returns (uint256) {
        sink(inner(x));
        s = 7;
        return s;
    }
}
