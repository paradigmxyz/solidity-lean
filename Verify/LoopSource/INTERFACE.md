# Verify/LoopSource interface

The loop route exports two things. Other lanes use them by name, and this file gives their exact
Lean signatures. The gas lane (`Verify/Gas/FixedFuel/**`) consumes the loop record and its step
relation. The certify driver's Statement consumes the generic link. The source is
`Verify/LoopSource/Generic/Interface.lean` and `Verify/LoopSource/Generic/Statement.lean`. A change to
any signature below is a change to this file in the same commit.

## Loop record and per-iteration step (for the gas lane)

```lean
namespace Verify.LoopSource.Interface
open SolidCore.Solidity.Source SolidCore.Refinement.Generic SolidCore.Refinement.Generic.Loop

structure LoopRecord where
  H : SymState          -- the loop header; its fresh words are what the loop changes
  P : Val → Prop        -- the invariant, over header valuations
  m : Val → Nat         -- the measure (ranking function), over header valuations
  c : WExpr             -- the erased loop condition
  bb : Br               -- the body's tree at the header

def LoopRecord.Obl (L : LoopRecord) (k : Nat) (E : EraseEnv) (ctx : Context) (cnd : Expr)
    (post body : Stmt) (Q : Result → Prop) : Prop :=
  ForObl k E ctx cnd post body L.H L.P L.m Q L.c L.bb

def LoopRecord.Step (L : LoopRecord) (σ σ' : Val) : Prop :=
  L.P σ ∧ L.c.eval σ ≠ 0 ∧ L.P σ' ∧ L.m σ' < L.m σ

inductive LoopRecord.Steps (L : LoopRecord) : Nat → Val → Prop
  | done (σ : Val) : Steps L 0 σ
  | step {σ σ' : Val} {n : Nat} : L.Step σ σ' → Steps L n σ' → Steps L (n + 1) σ

theorem LoopRecord.steps_le {L : LoopRecord} {n : Nat} {σ : Val} (h : L.Steps n σ) : n ≤ L.m σ

def LoopRecord.fuelBound (L : LoopRecord) (σ0 : Val) (k : Nat) : Nat := L.m σ0 + k + 2

theorem LoopRecord.step_of_back {L : LoopRecord} {E : EraseEnv} {ctx : Context} {σ : Val}
    {S : SymState} (hp : L.P σ) (hc : L.c.eval σ ≠ 0) (h : Back E ctx L.H L.P L.m σ S) :
    ∃ σ', L.Step σ σ' ∧ ∀ rt, StmtRel σ E ctx rt S → StmtRel σ' E ctx rt L.H

theorem LoopRecord.forLoop_ends {L : LoopRecord} {k k0 : Nat} {E : EraseEnv} {ctx : Context}
    {init : Stmt} {cnd : Expr} {post body : Stmt} {Q : Result → Prop}
    (h : L.Obl k E ctx cnd post body Q) {rt rt1 : Runtime}
    (hinit : Stmt.eval k0 E.tbl ctx rt.pushScope init = .done (.ok (.normal rt1)))
    {σ0 : Val} (hp0 : L.P σ0) (hrel0 : StmtRel σ0 E ctx rt1 L.H) (fuel : Nat)
    (hf : L.fuelBound σ0 k ≤ fuel) (hk0 : k0 + 1 ≤ fuel) :
    ∃ r, Stmt.eval fuel E.tbl ctx rt (.forLoop init cnd post body) =
      .done (.ok (r.mapRuntime Runtime.popScope)) ∧ Q r
end Verify.LoopSource.Interface
```

Solar's loop-head manifest (`*.loop-heads.json`) names the header's words. Its Lean form is
`Verify.LoopSource.LoopMap` (`LoopMap.lean`): `LoopMap.word (M : LoopMap) (H : SymState) (x : String) :
Option WExpr` maps each SMT name to the header word that `LoopRecord.H` carries.

## Generic whole-Statement link (for the driver Statement)

```lean
namespace Verify.LoopSource.Generic

def selCall (sel : Nat) (σ : List (Nat × Nat)) (args : List Nat) : Call
def ArgsOk (fn : FunctionDef) (ws : List Nat) (args : List Nat) : Prop :=
  args.length = fn.params.length ∧ (∀ a ∈ args, a < 2 ^ 256) ∧ argsClean ws args = true
def SelCall (sel : Nat) (fn : FunctionDef) (ws : List Nat) (call : Call) : Prop :=
  ∃ σ args, ArgsOk fn ws args ∧ call = selCall sel σ args
def OnTree (sel : Nat) (fn : FunctionDef) (ws : List Nat) (T : Tree)
    (Q : Call → Observable → Prop) : Prop :=
  ∀ σ args, ArgsOk fn ws args →
    Q (selCall sel σ args) (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs

def GenericLink : Prop :=
  ∀ (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (sel : Nat) (fn : FunctionDef)
    (ws : List Nat) (b : Br) (T : Tree),
    sel < 2 ^ 32 → c.core.findFunctionBySelector? sel = some fn →
    widthsOf fn.params fn.paramAbiCleanups = some ws → fn.returns.all wordBinding = true →
    BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b →
    brTree fn (argFacts ws 0) b = some T →
    ∀ (code : ByteArray) (Allowed Post : Call → Observable → Prop) (G : Call → Nat),
      OnTree sel fn ws T Allowed → OnTree sel fn ws T Post →
      Shapes.Equiv (solidCoreRuntime fuel) c code (SelCall sel fn ws) →
      Shapes.Resources (solidCoreRuntime fuel) c code (SelCall sel fn ws) G →
      Shapes.Certified (solidCoreRuntime fuel) c code (SelCall sel fn ws) Allowed Post G

theorem generic_link : GenericLink   -- Generic/Link.lean
end Verify.LoopSource.Generic
```

## What crosses between lanes

The loop lane proves `BodyRuns` for a function containing loops by building a `LoopRecord` per
loop, proving its `Obl`, and applying `forLoop_ends`. `generic_link` then turns that into the
Statement. Its `Shapes.Equiv` and `Shapes.Resources` premises are the bytecode side, which is
outside this lane.

The gas lane's fixed-fuel stage takes a `LoopRecord` and its `Obl`. It bounds iterations by
`steps_le` (at most `m σ0`), and bounds source fuel by `fuelBound`. It owes `Shapes.Resources`
for the loop's bytecode.

## Scope

The subset these signatures cover:

- functions whose arguments and returns are words, with clean ABI decoding (`widthsOf`, `wordBinding`);
- `for` / `while` loops whose condition, body and update the generic stage erases (no nested loop,
  no `break` / `continue`, no unerased internal call);
- a source semantics of `solidCoreRuntime` (a contract whose constructor takes arguments).

Counter's `bump` is the only test instance (`MirLink/`). Nothing in `Generic/` names a
contract, a selector, a file or a hash.
