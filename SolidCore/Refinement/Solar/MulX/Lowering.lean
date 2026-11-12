import SolidCore.Refinement.Generic.Value
import SolidCore.Refinement.KernelCopies
import SolidCore.Refinement.KernelRfl
import SolidCore.Refinement.Source.MulX
import mulx.gen.Main.Stage0

/-!
# Narrow checked multiplication: the generic source stage on solar's own module

The test contract scripts/refinement/mulx/mul.sol (sha256
50ef03a3c5724105509c3ed40b7ee7d92ea43b5d48a67d0e6722b26806dd4980),

    contract Main { uint8 x8; uint16 y16 = 3; uint256 z;
      function m(uint8 a, uint16 b) external { x8 *= a; y16 *= b; }
      function n(uint8 a, uint16 b, uint256 c) external returns (uint256) {
        z = uint256(a) * b * c; return z; } }

has checked `uint8` and `uint16` compound multiplications into two fields packed in slot 0
(`x8` at byte 0, `y16` at bytes 1 and 2), a constructor that leaves slot 0 = `3 * 256`, and a
`uint256` product of widened narrow parameters (`uint256(a) * b`, which cannot overflow, then
`* c`, which can). `SolarTV.Export.Main.stage0` is solar's first lowered MIR module for it,
exported by `solar -Zemit-lean-stages` at solar a8179dfc with `-Zcheck-analyses=false` into
solar's solar-tv/milestone/mulx and imported from there (`mulx.gen.Main.Stage0`, sha256
2b9c8cec1601216327fccf673b46da96524d9a9f370a59ba48c0e8c681ab04d3, the export manifest's), the
same module whose backend stages solar's milestone proves, so that the two compose
(Certified.lean). solar checks `x8 *= a` and `y16 *= b` with one range check each on the
exact product, joined by `or`; it drops the check of `uint256(a) * b` by its range analysis
and checks `* c` with `or (eq c 0) (eq (div p c) ab)`, branching to success when it holds.
SolidCore's core (`coreLit`, solc 0.8.35's AST through scripts/solc_ast_to_lean_source.py
into Source/MulX.lean and `TypeCheck.CheckedInput.contract`, printed and copied) checks both
products with `uint256`'s mul overflow check and then each narrow cleanup.

* `selM_eq`, `selN_eq`, `selector_eq`: the selectors of `m` and `n` by Keccak-256, each
  checked alone, so `ABI.selectorFromSignature` is `selectorTable`;
* `shape_eq`: `Main` type checks, its core is `coreLit` and its constructor leaves slot 0 =
  `3 * 256`, by one kernel conversion check (`kernel_rfl`) that evaluates the type checker
  once, on copies that read the selectors from `selectorTable`; there is no `Bool`
  recognizer of `coreLit`, whose `match` on the whole literal and `split` cost 3 GB and
  half a minute to elaborate;
* `check_m`, `check_n`: `Generic.check` accepts stage0 for `m` and for `n`
  (`decide +kernel`), so `check_stage0` for both;
* `lowering`: the stage from the deployed storage, under every oracle (`Generic.stageDeployed`);
* `loweringAt`: the stage from any storage that writes slot 0 (`Generic.stageAt`);
* `checkValue_stage0`: `Generic.checkValue` accepts stage0 for both functions (`decide +kernel`):
  `m` and `n` are not payable, and stage0 reverts with empty output on a call of either with a
  value other than 0, so `loweringValue` and `loweringAtValue` are `lowering` and `loweringAt`
  at every value below `2 ^ 256` (`Generic.stageDeployedValue`, `Generic.stageAtValue`);
  `checkValue_rejects_payable`: it rejects stage0 with the dispatcher's value check dropped;
* `check_rejects_unchecked`: the check rejects stage0 with `m`'s `uint8` check dropped from
  its panic branch, and `check_rejects_add`: with `n`'s second `mul` compiled as `add`.

The names of solar's stages (`SolarTV.Export.Main`) are those of w1's, w4's and c4's too, so
this module is built by `lake build SolidCoreSolarMulX`, outside the library root.

No sorry, native_decide or bv_decide: `decide +kernel` and `kernel_rfl` are the kernel's
evaluation, and the theorems depend on propext, Classical.choice and Quot.sound only (pinned
below).
-/

namespace SolidCore.Refinement.Solar.MulX

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Solidity SolidCore.Solidity.Source

/-- The interpreter fuel of SolidCore's runs. -/
def fuel : Nat := 4096

/-- The interpreter fuel of the symbolic run of the module: blocks along each path. -/
def mirFuel : Nat := 16

/-- SolidCore's checked `Main`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract Source.MulX.importedSourceUnit "Main"

/-- The selector of `m(uint8,uint16)`. -/
abbrev mSel : Nat := 0x16ea58cb

/-- The selector of `n(uint8,uint16,uint256)`. -/
abbrev nSel : Nat := 0x9db20e58

/-- `m` and its parameters. -/
def fnM : Fn := ⟨mSel, [.uint 8, .uint 16]⟩

/-- `n` and its parameters. -/
def fnN : Fn := ⟨nSel, [.uint 8, .uint 16, .uint 256]⟩

/-- Both functions of `Main`. -/
def fns : List Fn := [fnM, fnN]

/-- SolidCore's core contract of `Main`, as the type checker leaves it. -/
def coreLit : Contract :=
  { storageFields := [{ name := "x8",
                        slot := 0,
                        ty? := some (SolidCore.Solidity.Source.Ty.uint256),
                        layout? := some (SolidCore.Solidity.Source.StorageLayout.scalar
                                     (SolidCore.Solidity.Source.Ty.uint256)),
                        transient := false,
                        packedOffset := 0,
                        packedBytes := 1,
                        packedSigned := false },
                      { name := "y16",
                        slot := 0,
                        ty? := some (SolidCore.Solidity.Source.Ty.uint256),
                        layout? := some (SolidCore.Solidity.Source.StorageLayout.scalar
                                     (SolidCore.Solidity.Source.Ty.uint256)),
                        transient := false,
                        packedOffset := 1,
                        packedBytes := 2,
                        packedSigned := false },
                      { name := "z",
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
    functions := [{ name := "m",
                    selector? := some 384456907,
                    payable := false,
                    params := [{ name := "a", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false },
                               { name := "b", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 8,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 16],
                    returns := [],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "a")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   8
                                   (SolidCore.Solidity.Source.Expr.var "a")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "b")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   16
                                   (SolidCore.Solidity.Source.Expr.var "b")),
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.mul))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 8))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "x8"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "a")),
                                  SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.mul))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 16))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "y16"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "b"))]],
                    dispatchId? := none },
                  { name := "n",
                    selector? := some 2645691992,
                    payable := false,
                    params := [{ name := "a", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false },
                               { name := "b", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false },
                               { name := "c", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 8,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 16,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "a")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   8
                                   (SolidCore.Solidity.Source.Expr.var "a")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "b")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   16
                                   (SolidCore.Solidity.Source.Expr.var "b")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "c")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "c")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.assign
                                    (SolidCore.Solidity.Source.LValue.storage "z")
                                    (SolidCore.Solidity.Source.Expr.castOp
                                      (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                      256
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.binary
                                          (SolidCore.Solidity.Source.BinaryOp.mul)
                                          (SolidCore.Solidity.Source.Expr.castOp
                                            (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                            256
                                            (SolidCore.Solidity.Source.Expr.castOp
                                              (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                              256
                                              (SolidCore.Solidity.Source.Expr.binary
                                                (SolidCore.Solidity.Source.BinaryOp.mul)
                                                (SolidCore.Solidity.Source.Expr.castOp
                                                  (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                                  256
                                                  (SolidCore.Solidity.Source.Expr.castOp
                                                    (SolidCore.Solidity.Source.CastKind.uintCast)
                                                    256
                                                    (SolidCore.Solidity.Source.Expr.var "a")))
                                                (SolidCore.Solidity.Source.Expr.castOp
                                                  (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                                  256
                                                  (SolidCore.Solidity.Source.Expr.var "b")))))
                                          (SolidCore.Solidity.Source.Expr.castOp
                                            (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                            256
                                            (SolidCore.Solidity.Source.Expr.var "c"))))),
                                  SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.storageRead
                                         (SolidCore.Solidity.Source.StorageReadMode.ref)
                                         "z"
                                         [])]]],
                    dispatchId? := none },
                  { name := "__internal_m(uint8,uint16)#[SolidCore.Solidity.Ty.uint 8, SolidCore.Solidity.Ty.uint 16]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "a", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false },
                               { name := "b", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 8,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 16],
                    returns := [],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "a")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   8
                                   (SolidCore.Solidity.Source.Expr.var "a")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "b")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   16
                                   (SolidCore.Solidity.Source.Expr.var "b")),
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.mul))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 8))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "x8"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "a")),
                                  SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.mul))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 16))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "y16"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "b"))]],
                    dispatchId? := none },
                  { name := "__internal_n(uint8,uint16,uint256)#[SolidCore.Solidity.Ty.uint 8, SolidCore.Solidity.Ty.uint 16, SolidCore.Solidity.Ty.uint 256]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "a", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false },
                               { name := "b", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false },
                               { name := "c", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 8,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 16,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "a")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   8
                                   (SolidCore.Solidity.Source.Expr.var "a")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "b")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   16
                                   (SolidCore.Solidity.Source.Expr.var "b")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "c")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "c")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.assign
                                    (SolidCore.Solidity.Source.LValue.storage "z")
                                    (SolidCore.Solidity.Source.Expr.castOp
                                      (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                      256
                                      (SolidCore.Solidity.Source.Expr.castOp
                                        (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                        256
                                        (SolidCore.Solidity.Source.Expr.binary
                                          (SolidCore.Solidity.Source.BinaryOp.mul)
                                          (SolidCore.Solidity.Source.Expr.castOp
                                            (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                            256
                                            (SolidCore.Solidity.Source.Expr.castOp
                                              (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                              256
                                              (SolidCore.Solidity.Source.Expr.binary
                                                (SolidCore.Solidity.Source.BinaryOp.mul)
                                                (SolidCore.Solidity.Source.Expr.castOp
                                                  (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                                  256
                                                  (SolidCore.Solidity.Source.Expr.castOp
                                                    (SolidCore.Solidity.Source.CastKind.uintCast)
                                                    256
                                                    (SolidCore.Solidity.Source.Expr.var "a")))
                                                (SolidCore.Solidity.Source.Expr.castOp
                                                  (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                                  256
                                                  (SolidCore.Solidity.Source.Expr.var "b")))))
                                          (SolidCore.Solidity.Source.Expr.castOp
                                            (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                            256
                                            (SolidCore.Solidity.Source.Expr.var "c"))))),
                                  SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.storageRead
                                         (SolidCore.Solidity.Source.StorageReadMode.ref)
                                         "z"
                                         [])]]],
                    dispatchId? := none }] }

/-! ## The selectors

The type checker computes each external function's selector by Keccak-256 of its
signature, which costs the kernel about 400 MB a hash. Each is checked once, alone, and
the check of the shape below runs on copies that read them from a table. -/

/-- `m`'s selector, by Keccak-256 of its signature. -/
def selM : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "m(uint8,uint16)"

/-- `n`'s selector, by Keccak-256 of its signature. -/
def selN : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "n(uint8,uint16,uint256)"

kernel_rfl selM_eq selM mSel
kernel_rfl selN_eq selN nSel

/-- `ABI.selectorFromSignature`, with `Main`'s two signatures by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "m(uint8,uint16)" then mSel
  else if s = "n(uint8,uint16,uint256)" then nSel
  else SolidCore.Solidity.Source.ABI.selectorFromSignature s

theorem selector_eq : SolidCore.Solidity.Source.ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  split
  · next h => subst h; exact selM_eq
  · split
    · next h => subst h; exact selN_eq
    · rfl

/-- The storage the constructor leaves: `x8 = 0` in the low byte of slot 0, `y16 = 3` in the
next two. -/
def deployed : List (Nat × Nat) := [(0, 3 * 256)]

/-- SolidCore's checked core of `Main`, and whether its constructor leaves exactly `deployed`
and no logs, when `Main` type checks. -/
def shape? : Option (Contract × Bool) :=
  match contract? with
  | .ok c => some (c.core, Wide.deployedAt fuel c deployed)
  | .error _ => none

-- `shape_eq : shape? = some (coreLit, true)`: `Main` type checks, its core is `coreLit` and its
-- constructor leaves exactly `deployed`, by the kernel's conversion check on the copy of
-- `shape?` that reads the selectors from `selectorTable` (`selector_eq`): one check evaluates
-- the type checker once and hashes nothing, where a `Bool` test of the core would need a
-- decision procedure for equality of cores (`KernelRfl.lean`).
kernel_rfl shape_eq shape? (some (coreLit, true)) using selector_eq

/-! ## The check on solar's module -/

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `m`. -/
theorem check_m :
    Generic.check fuel mirFuel coreLit SolarTV.Export.Main.stage0 [fnM] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `n`. -/
theorem check_n :
    Generic.check fuel mirFuel coreLit SolarTV.Export.Main.stage0 [fnN] = true := by
  decide +kernel

/-- The generic check accepts stage0 for both functions. -/
theorem check_stage0 :
    Generic.check fuel mirFuel coreLit SolarTV.Export.Main.stage0 fns = true := by
  have hm := check_m
  have hn := check_n
  simp only [Generic.check, List.all_cons, List.all_nil, Bool.and_true] at hm hn
  simp only [Generic.check, fns, List.all_cons, List.all_nil, Bool.and_true, hm, hn]

/-! ## Mutants the check rejects -/

/-- stage0 with each instruction of function `i` changed by `f`. -/
def mapFn (i : Nat) (f : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst) :
    SolarTV.MIR.Lowered.Module :=
  { SolarTV.Export.Main.stage0 with
    functions := SolarTV.Export.Main.stage0.functions.mapIdx fun j fn =>
      if j = i then { fn with blocks := fn.blocks.map fun b => { b with insts := b.insts.map f } }
      else fn }

/-- `m`'s panic condition without `x8`'s range check: `or v45 v45` for `or v33 v45`. -/
def dropX8Check : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .pure 76 .or [.value 33, b] => .pure 76 .or [b, b]
  | i => i

/-- `n`'s product `uint256(a) * b * c` with its second `mul` compiled as `add`. -/
def mulToAdd : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .pure 11 .mul args => .pure 11 .add args
  | i => i

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `m` without `x8`'s overflow check. -/
theorem check_rejects_unchecked :
    Generic.check fuel mirFuel coreLit (mapFn 0 dropX8Check) [fnM] = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the check rejects `n` with `add` for its second `mul`. -/
theorem check_rejects_add :
    Generic.check fuel mirFuel coreLit (mapFn 1 mulToAdd) [fnN] = false := by
  decide +kernel

/-! ## The stage -/

/-- The checked contract has the core `coreLit`, and its constructor leaves exactly
`deployed`. -/
theorem deployed_of {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    c.core = coreLit ∧ ∃ d, Wide.DeployedAt fuel c d deployed := by
  have h := shape_eq
  unfold shape? at h
  rw [hc] at h
  obtain ⟨hk, hd⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hk, Wide.deployedAt_of hd⟩

/-- **The source stage of `Main` from the deployed storage**: every call of `m` and `n` on any
argument words, no value, from the storage the constructor leaves, under every oracle. -/
theorem lowering (o : SolarTV.Machine.Oracle)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 (fullScope fns deployed) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.stageDeployed o hd (by rw [hk]; exact check_stage0)

/-- The calls from any storage that writes slot 0, the slot the constructor writes. -/
def scopeAt : Call → Prop :=
  fun call => ∃ σ, (∃ kv ∈ σ, kv.1 % 2 ^ 256 = 0) ∧ fullScope fns σ call

/-- **The source stage of `Main` from any storage that writes slot 0**: every call of `m` and
`n` on any argument words, no value, under every oracle. -/
theorem loweringAt (o : SolarTV.Machine.Oracle)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 scopeAt := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  refine SolarTV.Stage.mono (Generic.stageAt o hd (by rw [hk]; exact check_stage0)) ?_
  rintro call ⟨σ, ⟨kv, hkv, h0⟩, hs⟩
  refine ⟨σ, ?_, hs⟩
  intro kv' hkv'
  simp only [deployed, List.mem_singleton] at hkv'
  subst hkv'
  exact ⟨kv, hkv, h0⟩

/-- info: 'SolidCore.Refinement.Solar.MulX.selector_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms selector_eq

/-- info: 'SolidCore.Refinement.Solar.MulX.shape_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shape_eq

/-! ## The stage at every value -/

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: neither function is payable, and stage0 reverts with empty output on
a call of either with a value other than 0. -/
theorem checkValue_stage0 :
    Generic.checkValue mirFuel coreLit SolarTV.Export.Main.stage0 fns = true := by
  decide +kernel

/-- The dispatcher's value check `ne(callvalue, 0)` as `ne(0, 0)`: a dispatcher that accepts a
value. -/
def dropValueCheck : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .ne dst _ b => .ne dst (.const 0) b
  | i => i

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the value check rejects stage0 with the dispatcher's value check
dropped (function 3 is the entry). -/
theorem checkValue_rejects_payable :
    Generic.checkValue mirFuel coreLit (mapFn 3 dropValueCheck) fns = false := by
  decide +kernel

/-- **The source stage of `Main` from the deployed storage, at every value**: every call of `m`
and `n` on any argument words, with any value below `2 ^ 256`, from the storage the constructor
leaves, under every oracle. -/
theorem loweringValue (o : SolarTV.Machine.Oracle)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0
      (fun call => ∃ v, Generic.fullScopeValue fns deployed v call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.stageDeployedValue o hd (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0)

/-- The calls from any storage that writes slot 0, with any value. -/
def scopeAtValue : Call → Prop :=
  fun call => ∃ σ v, (∃ kv ∈ σ, kv.1 % 2 ^ 256 = 0) ∧ Generic.fullScopeValue fns σ v call

/-- **The source stage of `Main` from any storage that writes slot 0, at every value**: every
call of `m` and `n` on any argument words, with any value below `2 ^ 256`, under every
oracle. -/
theorem loweringAtValue (o : SolarTV.Machine.Oracle)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 scopeAtValue := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  refine SolarTV.Stage.mono (Generic.stageAtValue o hd (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0)) ?_
  rintro call ⟨σ, v, ⟨kv, hkv, h0⟩, hs⟩
  refine ⟨σ, v, ?_, hs⟩
  intro kv' hkv'
  simp only [deployed, List.mem_singleton] at hkv'
  subst hkv'
  exact ⟨kv, hkv, h0⟩

/-- info: 'SolidCore.Refinement.Solar.MulX.check_stage0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms check_stage0

/-- info: 'SolidCore.Refinement.Solar.MulX.check_rejects_unchecked' depends on axioms: [propext] -/
#guard_msgs in
#print axioms check_rejects_unchecked

/-- info: 'SolidCore.Refinement.Solar.MulX.check_rejects_add' depends on axioms: [propext] -/
#guard_msgs in
#print axioms check_rejects_add

/-- info: 'SolidCore.Refinement.Solar.MulX.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering

/-- info: 'SolidCore.Refinement.Solar.MulX.loweringAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringAt

/-- info: 'SolidCore.Refinement.Solar.MulX.checkValue_stage0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkValue_stage0

/-- info: 'SolidCore.Refinement.Solar.MulX.checkValue_rejects_payable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkValue_rejects_payable

/-- info: 'SolidCore.Refinement.Solar.MulX.loweringValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringValue

/-- info: 'SolidCore.Refinement.Solar.MulX.loweringAtValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringAtValue

end SolidCore.Refinement.Solar.MulX
