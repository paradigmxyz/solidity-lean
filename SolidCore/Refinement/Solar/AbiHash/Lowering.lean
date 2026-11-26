import SolidCore.Refinement.Generic.Value
import SolidCore.Refinement.KernelCopies
import SolidCore.Refinement.KernelRfl
import SolidCore.Refinement.Source.AbiHash
import abi_hash.gen.AbiHash.Stage0

/-!
# abi_hash: Keccak-256 of ABI-encoded memory through the generic source stage

scripts/refinement/mem/abi_hash.sol,

    contract AbiHash {
      function hashPair(uint256 a, uint256 b) external pure returns (uint256) {
        return uint256(keccak256(abi.encode(a, b))); } }

SolidCore evaluates `keccak256(abi.encode(a, b))` on the ABI encoding of the two words, 64
bytes; solar's first lowered MIR stores the two words at memory 0 and 32 and hashes those 64
bytes with `keccak256`. The generic erasure reads the source expression as `WExpr.hash a b`
(`Generic.hashPair?`, `Generic.eval_hash_pair`) and the symbolic run reads the module's hash of
the two memory words as the same `WExpr.hash`, so the check compares them structurally. Both
sides are Keccak-256 of the same 64 bytes: the stage holds under every oracle whose Keccak-256 of
two words is SolidCore's (`Generic.HashOk`, part of `Generic.SourceEnvOk`), with no
injectivity or separation premise: equal inputs give equal hashes and nothing more is used.

* `shape_eq`: `AbiHash` type checks, its core is `coreLit`, its constructor leaves no storage;
* `check_stage0`, `checkValue_stage0`: the generic check with the environment flags accepts
  stage0 (`decide +kernel`), at no value and at any value;
* `check_rejects_order`, `check_rejects_size`, `check_rejects_arg`: it rejects stage0 hashing
  the words in the other order, hashing only the first word, and returning the first argument;
* `lowering`, `loweringValue`: the stage from SolidCore to stage0 on every call of `hashPair`.

No sorry, native_decide or bv_decide.
-/

namespace SolidCore.Refinement.Solar.AbiHash

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Solidity SolidCore.Solidity.Source

/-- The interpreter fuel of SolidCore's runs. -/
def fuel : Nat := 4096

/-- The interpreter fuel of the symbolic run of the module: steps along each path. -/
def mirFuel : Nat := 40

/-- SolidCore's checked `AbiHash`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract Source.AbiHash.importedSourceUnit "AbiHash"

/-- The selector of `hashPair(uint256,uint256)`. -/
abbrev hashPairSel : Nat := 0x66d82b2b

/-- `hashPair` and its parameters. -/
def fnHashPair : Fn := ⟨hashPairSel, [.uint 256, .uint 256]⟩

/-- The external function of `AbiHash`. -/
def fns : List Fn := [fnHashPair]

/-- SolidCore's core contract of `AbiHash`, as the type checker leaves it. -/
def coreLit : Contract :=
  { storageFields := [],
    immutableFields := [],
    eventDecls := [],
    errorDecls := [],
    functions := [{ name := "hashPair",
                    selector? := some 1725442859,
                    payable := false,
                    params := [{ name := "a",
                                 ty := SolidCore.Solidity.Source.Ty.uint256,
                                 isStorageRef := false },
                               { name := "b",
                                 ty := SolidCore.Solidity.Source.Ty.uint256,
                                 isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 256,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0",
                                  ty := SolidCore.Solidity.Source.Ty.uint256,
                                  isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "a")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "a")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "b")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "b")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.castOp
                                         (SolidCore.Solidity.Source.CastKind.uintCast)
                                         256
                                         (SolidCore.Solidity.Source.Expr.keccak256
                                           (SolidCore.Solidity.Source.Expr.encode
                                             (SolidCore.Solidity.Source.EncodeKind.plain)
                                             none
                                             []
                                             [SolidCore.Solidity.Source.Ty.uint256,
                                              SolidCore.Solidity.Source.Ty.uint256]
                                             [SolidCore.Solidity.Source.Expr.var "a",
                                              SolidCore.Solidity.Source.Expr.var "b"])))]]],
                    dispatchId? := none },
                  { name := "__internal_hashPair(uint256,uint256)#[SolidCore.Solidity.Ty.uint 256, SolidCore.Solidity.Ty.uint 256]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "a",
                                 ty := SolidCore.Solidity.Source.Ty.uint256,
                                 isStorageRef := false },
                               { name := "b",
                                 ty := SolidCore.Solidity.Source.Ty.uint256,
                                 isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 256,
                                         SolidCore.Solidity.Source.AbiCleanup.uint 256],
                    returns := [{ name := "_ret0",
                                  ty := SolidCore.Solidity.Source.Ty.uint256,
                                  isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "a")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "a")),
                               SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "b")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   256
                                   (SolidCore.Solidity.Source.Expr.var "b")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       256
                                       (SolidCore.Solidity.Source.Expr.castOp
                                         (SolidCore.Solidity.Source.CastKind.uintCast)
                                         256
                                         (SolidCore.Solidity.Source.Expr.keccak256
                                           (SolidCore.Solidity.Source.Expr.encode
                                             (SolidCore.Solidity.Source.EncodeKind.plain)
                                             none
                                             []
                                             [SolidCore.Solidity.Source.Ty.uint256,
                                              SolidCore.Solidity.Source.Ty.uint256]
                                             [SolidCore.Solidity.Source.Expr.var "a",
                                              SolidCore.Solidity.Source.Expr.var "b"])))]]],
                    dispatchId? := none }] }

/-! ## The selector

The type checker computes the selector by Keccak-256, which costs the kernel about 400 MB: it is
checked once, alone, and the check of the shape below reads it from a table. -/

/-- The selector of `hashPair(uint256,uint256)`, by Keccak-256 of its signature. -/
def selHashPair : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "hashPair(uint256,uint256)"

kernel_rfl selHashPair_eq selHashPair hashPairSel

/-- `ABI.selectorFromSignature`, with `AbiHash`'s signature by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "hashPair(uint256,uint256)" then hashPairSel
  else SolidCore.Solidity.Source.ABI.selectorFromSignature s

theorem selector_eq : SolidCore.Solidity.Source.ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  split
  · next h => subst h; exact selHashPair_eq
  · rfl

/-- SolidCore's checked core of `AbiHash`, and whether its constructor leaves no storage and no
logs, when `AbiHash` type checks. -/
def shape? : Option (Contract × Bool) :=
  match contract? with
  | .ok c => some (c.core, Wide.deployedAt fuel c [])
  | .error _ => none

kernel_rfl shape_eq shape? (some (coreLit, true)) using selector_eq

/-! ## The check on solar's module -/

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for `hashPair`. -/
theorem check_stage0 :
    Generic.check fuel mirFuel coreLit SolarTV.Export.AbiHash.stage0 fns .all = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: `hashPair` is not payable, and stage0 reverts with empty output on a
call with a value other than 0. -/
theorem checkValue_stage0 :
    Generic.checkValue mirFuel coreLit SolarTV.Export.AbiHash.stage0 fns .all = true := by
  decide +kernel

/-! ## Mutants the check rejects -/

/-- stage0 with each instruction of function `i` changed by `f`. -/
def mapFn (i : Nat) (f : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst) :
    SolarTV.MIR.Lowered.Module :=
  { SolarTV.Export.AbiHash.stage0 with
    functions := SolarTV.Export.AbiHash.stage0.functions.mapIdx fun j fn =>
      if j = i then { fn with blocks := fn.blocks.map fun b => { b with insts := b.insts.map f } }
      else fn }

/-- `hashPair` storing the two words in each other's place before hashing them. -/
def swapWords : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect none .mstore [.const o, a] =>
    .effect none .mstore [.const (if o = 0 then 32 else if o = 32 then 0 else o), a]
  | i => i

/-- `hashPair` hashing only the first word. -/
def shortHash : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect d .keccak256 [o, .const n] => .effect d .keccak256 [o, .const (if n = 64 then 32 else n)]
  | i => i

/-- `hashPair` returning its first argument rather than the hash. -/
def noHash : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .effect (some d) .keccak256 _ => .effect (some d) .calldataload [.const 4]
  | i => i

set_option maxRecDepth 100000 in
theorem check_rejects_order :
    Generic.check fuel mirFuel coreLit (mapFn 0 swapWords) fns .all = false := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem check_rejects_size :
    Generic.check fuel mirFuel coreLit (mapFn 0 shortHash) fns .all = false := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem check_rejects_arg :
    Generic.check fuel mirFuel coreLit (mapFn 0 noHash) fns .all = false := by
  decide +kernel

/-! ## The stage -/

/-- The checked contract has the core `coreLit`, and its constructor leaves no storage. -/
theorem deployed_of {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    c.core = coreLit ∧ ∃ d, Wide.DeployedAt fuel c d [] := by
  have h := shape_eq
  unfold shape? at h
  rw [hc] at h
  obtain ⟨hk, hd⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hk, Wide.deployedAt_of hd⟩

/-- **The source stage of `AbiHash`**: every call of `hashPair` on any argument words, no
value, from any storage, under every oracle whose caller and Keccak-256 of two words are
SolidCore's (`Generic.SourceEnvOk`). -/
theorem lowering (o : SolarTV.Machine.Oracle) (henv : Generic.SourceEnvOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.AbiHash.stage0 (fun call => ∃ σ, fullScope fns σ call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.stageEnv o henv hd (by rw [hk]; exact check_stage0)

/-- **The source stage of `AbiHash` at every value**. -/
theorem loweringValue (o : SolarTV.Machine.Oracle) (henv : Generic.SourceEnvOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.AbiHash.stage0 (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.stageValueEnv o henv hd (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0)

#print axioms shape_eq
#print axioms check_stage0
#print axioms checkValue_stage0
#print axioms check_rejects_order
#print axioms check_rejects_size
#print axioms check_rejects_arg
#print axioms lowering
#print axioms loweringValue

end SolidCore.Refinement.Solar.AbiHash
