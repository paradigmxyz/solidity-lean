import Verify.AnyCaller.Theorem

/-!
# Any-caller tests

A contract whose result is its caller,

    contract Who { function who() external view returns (uint256) {
      return uint256(uint160(msg.sender)); } }

with its core written in the type checker's shape (as Generic/MulTest.lean does) and `whoStage0`, a
lowered MIR module in the shape of solar's first lowered MIR that returns `CALLER`.

Positive, two distinct callers from one check:

* `check_who` / `checkValue_who`: `checkSym` and `checkValue ... .allSym` accept the module
  (`decide +kernel`);
* `who_stage_two_callers`: from that one check, the stage from SolidCore's run sent by `0x2000` and the
  one sent by `0xbeef`, each under its own oracle;
* `who_sees_caller`: the callers are told apart: the erased source tree and the module's symbolic tree
  each return `0x2000` for one and `0xbeef` for the other, so neither stage is about a constant.

Negatives, each failing closed:

* `msg.sender` misuse: `pinned_rejected` (the module returns the constant `0x2000` instead of `CALLER`:
  the fixed-caller check `check ... .callerOnly` accepts it, `pinned_fixed_accepts`, and `checkSym`
  refuses it) and `address_rejected` (it returns `ADDRESS`);
* caller aliasing: `alias_self` (the contract's own address is no context of the statement) and
  `alias_oracle` (an oracle for one caller says nothing about another);
* overflow: `overflow_alias` (`2 ^ 160 + 0x2000` truncates to the same `CALLER` as `0x2000`) and
  `overflow_rejected` (no oracle is an oracle for it, and it is no context).
-/

namespace SolidCore.Verify.AnyCaller.Tests

open SolarTV SolarTV.MIR.Lowered SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Solidity.Source

/-- `who`, as the type checker leaves it. -/
def whoFn : FunctionDef :=
                  { name := "who",
                    selector? := some 0xd6d21dfd,
                    payable := false,
                    params := [],
                    paramAbiCleanups := [],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256,
                                  isStorageRef := false }],
                    body := Stmt.block [Stmt.returnValues [Expr.caller]],
                    dispatchId? := none }

/-- The core of `Who`. -/
def whoCore : Contract :=
  { storageFields := [], immutableFields := [], eventDecls := [], errorDecls := [],
    functions := [whoFn] }

/-- The selector of `who()`. -/
abbrev whoSel : Nat := 0xd6d21dfd

def whoFns : List Abi.Fn := [⟨whoSel, []⟩]

/-- `Who`'s module, with `who`'s result word `w` (function 0) and its dispatcher (function 1). -/
def stage0With (body : List Inst) : Module :=
  { entry := 1,
    functions := [
    -- @who
    { params := [],
      blocks := [⟨[], body, .ret (.const 0) (.const 32)⟩] },
    -- @entry
    { params := [],
      blocks := [
      ⟨[], [.effect (some 0) .callvalue [], .ne 2 (.value 0) (.const 0)], .branch (.value 2) 3 1⟩,
      ⟨[], [.effect (some 4) .calldataload [.const 0], .pure 6 .shr [.const 224, .value 4]],
        .switch (.value 6) 3 [(.const whoSel, 2)]⟩,
      ⟨[], [], .tailCall 0 []⟩,
      ⟨[], [], .revert (.const 0) (.const 0)⟩] }] }

/-- `who` returns `CALLER`. -/
def whoStage0 : Module :=
  stage0With [.effect (some 1) .caller [], .effect none .mstore [.const 0, .value 1]]

/-- `who` returns the constant `callerWord` (`0x2000`), right only for that one caller. -/
def pinnedStage0 : Module :=
  stage0With [.effect none .mstore [.const 0, .const 0x2000]]

/-- `who` returns `ADDRESS`, the contract's own address, instead of its caller. -/
def addressStage0 : Module :=
  stage0With [.effect (some 1) .address [], .effect none .mstore [.const 0, .value 1]]

/-! ## Positive -/

set_option maxRecDepth 100000 in
theorem check_who : checkSym 4096 16 whoCore whoStage0 whoFns = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem checkValue_who : checkValue 16 whoCore whoStage0 whoFns .allSym = true := by
  decide +kernel

/-- **Two distinct callers from one check**: for every checked contract whose core is `whoCore`,
the stage sent by `0x2000` and the stage sent by `0xbeef`. -/
theorem who_stage_two_callers {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : c.core = whoCore)
    {d : SolidCore.Solidity.Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt 4096 c d s) :
    Stage (solidCoreFrom 0x2000 4096) (moduleSem (oracleAt 0x2000)) c whoStage0 (scope s whoFns) ∧
    Stage (solidCoreFrom 0xbeef 4096) (moduleSem (oracleAt 0xbeef)) c whoStage0 (scope s whoFns) :=
  have hchk : checkSym 4096 16 c.core whoStage0 whoFns = true := hc ▸ check_who
  have hval : checkValue 16 c.core whoStage0 whoFns .allSym = true := hc ▸ checkValue_who
  ⟨stageAtValueFrom 0x2000 (by decide) _ (fromOk_of_okAt (by decide) (oracleAt_okAt (by decide)))
      hd hchk hval,
   stageAtValueFrom 0xbeef (by decide) _ (fromOk_of_okAt (by decide) (oracleAt_okAt (by decide)))
      hd hchk hval⟩

/-- A valuation of the trees' words sent by `a`. -/
def valAt (a : Nat) : Val := ⟨[], fun _ => 0, fun _ _ => 0, a⟩

/-- The output of `who` on the source side and the module side, sent by `a`. -/
def outputs (a : Nat) : Option (List Nat × List Nat) :=
  match eraseFnSym (envOf whoCore) 4096 whoFn,
      symTree whoStage0 whoSel 0 16 .allSym with
  | some t1, some t2 => some ((t1.eval (valAt a)).output, (t2.eval (valAt a)).output)
  | _, _ => none

/-- The word of 32 big-endian bytes. -/
def word (bs : List Nat) : Nat := bs.foldl (fun acc b => acc * 256 + b) 0

/-- Both trees' outputs are 32 bytes whose word is the caller `a`. -/
def returnsCaller (a : Nat) : Bool :=
  match outputs a with
  | some (x, y) => x == y && x.length == 32 && word x == a
  | none => false

set_option maxRecDepth 100000 in
/-- **The callers are told apart**: both trees return the caller's word, `0x2000` for one and
`0xbeef` for the other. -/
theorem who_sees_caller :
    returnsCaller 0x2000 = true ∧ returnsCaller 0xbeef = true ∧ outputs 0x2000 ≠ outputs 0xbeef := by
  decide +kernel

/-! ## Negatives: `msg.sender` misuse -/

set_option maxRecDepth 100000 in
/-- The fixed-caller check accepts the pinned module: right for `callerWord` alone. -/
theorem pinned_fixed_accepts : check 4096 16 whoCore pinnedStage0 whoFns .callerOnly = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The check for every caller refuses it. -/
theorem pinned_rejected : checkSym 4096 16 whoCore pinnedStage0 whoFns = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Returning `ADDRESS` for `msg.sender` is refused. -/
theorem address_rejected : checkSym 4096 16 whoCore addressStage0 whoFns = false := by
  decide +kernel

/-! ## Negatives: caller aliasing -/

/-- The contract calling itself is no context of the statement. -/
theorem alias_self : ¬ SolidCore.Verify.Generic.Context.Ok ⟨selfAddress⟩ := not_ok_self

/-- An oracle for `0x2000` is no oracle for `0xbeef`: one caller's run says nothing of another's. -/
theorem alias_oracle : ¬ FromOk 0xbeef (oracleAt 0x2000) := fun h => by
  have := h.caller
  rw [show ((oracleAt 0x2000).caller.setWidth 256).toNat = 0x2000 by decide] at this
  omega

/-! ## Negatives: overflow -/

/-- `2 ^ 160 + 0x2000` truncates to `0x2000`'s `CALLER`. -/
theorem overflow_alias : oracleAt (2 ^ 160 + 0x2000) = oracleAt 0x2000 := by
  simp only [oracleAt]
  congr 1

/-- And it fails closed: no oracle is one for it, and it is no context. -/
theorem overflow_rejected :
    (∀ o, ¬ FromOk (2 ^ 160 + 0x2000) o) ∧
      ¬ SolidCore.Verify.Generic.Context.Ok ⟨2 ^ 160 + 0x2000⟩ :=
  ⟨not_fromOk_of_wide (by omega), fun h => by
    have h1 : 2 ^ 160 + 0x2000 < 2 ^ 160 := h.1
    omega⟩

/-- info: 'SolidCore.Verify.AnyCaller.Tests.who_stage_two_callers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms who_stage_two_callers

end SolidCore.Verify.AnyCaller.Tests
