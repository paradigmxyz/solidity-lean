import SolidCore.Refinement.Generic.Stage

/-!
# The generic check on checked multiplication

A test of the generic check's checked multiplication, which no corpus instance of the generic
stage exercises. The contract

    contract Main { uint8 a; uint256 c;
      function f(uint8 x) external returns (uint8) { a *= x; return a; }
      function g(uint256 x) external { c *= x; } }

has a `uint8` compound multiplication into a packed field and a `uint256` one. `coreLit` is
the core SolidCore's type checker leaves for it (solc 0.8.35's AST through
scripts/solc_ast_to_lean_source.py and `TypeCheck.CheckedInput.contract`, printed and copied).
`mulStage0` is a lowered MIR module written by hand in the shape of solar's first lowered MIR
(c4's Stage0.lean for the dispatcher, the argument checks and the packed write), with the
overflow checks solar's `lower-arithmetic` pass emits (crates/codegen/src/mir/transform/
lower_arithmetic.rs, `mul_overflow`): for `uint8`, whose operands' exact product fits in a
word, the range check `gt (mul a x) 255`; for `uint256`,
`iszero (or (iszero x) (eq (div (mul c x) x) c))`. solar's exporter is not part of this
checkout, so the module is not solar's output (Solar/MulX/Lowering.lean runs the check on
solar's own export of a narrow-mul contract); it checks that the canonical forms meet
SolidCore's checked `uint256` multiplication followed by its `uint8` cleanup:

* `check_mul`: `Generic.check` accepts `mulStage0` for both functions (`decide +kernel`);
* `check_rejects_wide`: it rejects the module with `uint8`'s range check against `2 ^ 16 - 1`;
* `check_rejects_quotient`: it rejects the module whose `uint256` check compares the quotient
  with `x` instead of `c`.
-/

namespace SolidCore.Refinement.Generic.MulTest

open SolidCore.Solidity.Source SolarTV.MIR.Lowered

/-- SolidCore's core contract of the test, as the type checker leaves it. -/
def coreLit : Contract :=
  { storageFields := [{ name := "a",
                        slot := 0,
                        ty? := some (SolidCore.Solidity.Source.Ty.uint256),
                        layout? := some (SolidCore.Solidity.Source.StorageLayout.scalar
                                     (SolidCore.Solidity.Source.Ty.uint256)),
                        transient := false,
                        packedOffset := 0,
                        packedBytes := 1,
                        packedSigned := false },
                      { name := "c",
                        slot := 1,
                        ty? := some (SolidCore.Solidity.Source.Ty.uint256),
                        layout? := some (SolidCore.Solidity.Source.StorageLayout.scalar
                                     (SolidCore.Solidity.Source.Ty.uint256)),
                        transient := false,
                        packedOffset := 0,
                        packedBytes := 32,
                        packedSigned := false }],
    immutableFields := [],
    eventDecls := [],
    errorDecls := [],
    functions := [{ name := "f",
                    selector? := some 824235060,
                    payable := false,
                    params := [{ name := "x", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 8],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "x")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   8
                                   (SolidCore.Solidity.Source.Expr.var "x")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.mul))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 8))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "a"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "x")),
                                  SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       8
                                       (SolidCore.Solidity.Source.Expr.storageRead
                                         (SolidCore.Solidity.Source.StorageReadMode.ref)
                                         "a"
                                         [])]]],
                    dispatchId? := none },
                  { name := "g",
                    selector? := some 3827312202,
                    payable := false,
                    params := [{ name := "x", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "x")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "x")),
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.mul))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "c"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "x"))]],
                    dispatchId? := none },
                  { name := "__internal_f(uint8)#[SolidCore.Solidity.Ty.uint 8]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "x", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 8],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "x")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   8
                                   (SolidCore.Solidity.Source.Expr.var "x")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.mul))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 8))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "a"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "x")),
                                  SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       8
                                       (SolidCore.Solidity.Source.Expr.storageRead
                                         (SolidCore.Solidity.Source.StorageReadMode.ref)
                                         "a"
                                         [])]]],
                    dispatchId? := none },
                  { name := "__internal_g(uint256)#[SolidCore.Solidity.Ty.uint 256]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "x", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "x")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "x")),
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.mul))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 256))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "c"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "x"))]],
                    dispatchId? := none }] }

/-- The selector of `f(uint8)`. -/
abbrev fSel : Nat := 824235060

/-- The selector of `g(uint256)`. -/
abbrev gSel : Nat := 3827312202

/-- Both functions and their parameters. -/
def fns : List SolidCore.Refinement.Abi.Fn := [⟨fSel, [.uint 8]⟩, ⟨gSel, [.uint 256]⟩]

/-- A lowered MIR module for the test, in the shape of solar's: `f` (function 0) checks the call
data size and `x`'s cleanliness, multiplies the low byte of slot 0 by `x` with the `uint8`
range check, writes the product back into the low byte and returns it; `g` (function 1)
multiplies slot 1 by `x` with the `uint256` check. -/
def mulStage0 : Module :=
  { entry := 2,
    functions := [
    -- @f
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 45) .calldatasize [],
         .pure 47 .lt [.value 45, .const 36],
         .effect (some 49) .calldataload [.const 4],
         .pure 51 .gt [.value 49, .const 255],
         .pure 71 .or [.value 47, .value 51]],
        .branch (.value 71) 3 4⟩,
      -- bb1
      ⟨[],
        [.effect none .mstore [.const 32, .const 17],
         .effect none .mstore [.const 0, .const 0x4e487b71]],
        .revert (.const 28) (.const 36)⟩,
      -- bb2
      ⟨[],
        [.pure 8 .and [.value 2, .const 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00],
         .pure 11 .or [.value 8, .value 34],
         .effect none .sstore [.const 0, .value 11],
         .pure 65 .and [.value 11, .const 255],
         .effect none .mstore [.const 0, .value 65]],
        .ret (.const 0) (.const 32)⟩,
      -- bb3
      ⟨[],
        [],
        .revert (.const 0) (.const 0)⟩,
      -- bb4
      ⟨[],
        [.effect (some 2) .sload [.const 0],
         .pure 69 .and [.value 2, .const 255],
         .pure 34 .mul [.value 69, .value 49],
         .pure 36 .gt [.value 34, .const 255]],
        .branch (.value 36) 1 2⟩] },
    -- @g
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 45) .calldatasize [],
         .pure 47 .lt [.value 45, .const 36]],
        .branch (.value 47) 3 4⟩,
      -- bb1
      ⟨[],
        [.effect none .mstore [.const 32, .const 17],
         .effect none .mstore [.const 0, .const 0x4e487b71]],
        .revert (.const 28) (.const 36)⟩,
      -- bb2
      ⟨[],
        [.effect none .sstore [.const 1, .value 34]],
        .stop⟩,
      -- bb3
      ⟨[],
        [],
        .revert (.const 0) (.const 0)⟩,
      -- bb4
      ⟨[],
        [.effect (some 49) .calldataload [.const 4],
         .effect (some 2) .sload [.const 1],
         .pure 34 .mul [.value 2, .value 49],
         .pure 40 .iszero [.value 49],
         .pure 41 .div [.value 34, .value 49],
         .pure 42 .eq [.value 41, .value 2],
         .pure 43 .or [.value 40, .value 42],
         .pure 44 .iszero [.value 43]],
        .branch (.value 44) 1 2⟩] },
    -- @entry
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 0) .callvalue [],
         .ne 2 (.value 0) (.const 0)],
        .branch (.value 2) 4 1⟩,
      -- bb1
      ⟨[],
        [.effect (some 4) .calldataload [.const 0],
         .pure 6 .shr [.const 224, .value 4]],
        .switch (.value 6) 4 [(.const fSel, 2), (.const gSel, 3)]⟩,
      -- bb2
      ⟨[],
        [],
        .tailCall 0 []⟩,
      -- bb3
      ⟨[],
        [],
        .tailCall 1 []⟩,
      -- bb4
      ⟨[],
        [],
        .revert (.const 0) (.const 0)⟩] }] }

/-- `mulStage0` with each instruction changed by `f`. -/
def mapInsts (f : Inst → Inst) : Module :=
  { mulStage0 with
    functions := mulStage0.functions.map fun fn =>
      { fn with blocks := fn.blocks.map fun b => { b with insts := b.insts.map f } } }

/-- `uint8`'s range check against `2 ^ 16 - 1`, the product's bound, instead of `255`. -/
def wideCheck : Inst → Inst
  | .pure 36 .gt [a, .const 255] => .pure 36 .gt [a, .const 65535]
  | i => i

/-- `uint256`'s check comparing the quotient with `x` instead of `c`. -/
def quotientCheck : Inst → Inst
  | .pure 42 .eq [a, .value 2] => .pure 42 .eq [a, .value 49]
  | i => i

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts the module for both functions. -/
theorem check_mul : check 4096 16 coreLit mulStage0 fns = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects a `uint8` product checked against `2 ^ 16 - 1`. -/
theorem check_rejects_wide : check 4096 16 coreLit (mapInsts wideCheck) fns = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects a `uint256` check against the wrong operand. -/
theorem check_rejects_quotient : check 4096 16 coreLit (mapInsts quotientCheck) fns = false := by
  decide +kernel

end SolidCore.Refinement.Generic.MulTest
