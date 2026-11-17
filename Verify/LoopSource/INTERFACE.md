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

## Loop bytecode equivalence (`Verify/LoopSource/Equiv/`)

The producer of `Shapes.Equiv` for a loop-carrying function. It never takes `Equiv`, or a stage
from the source to anything, as a premise. Its premises are:

- the source loop's `BodyRuns`, from the loop route;
- a cut-point certificate `C` whose check the kernel runs on the lowered MIR (`C.check … = some (le, li)`);
- obligations `Obl` on that check's leaves, stated over the source's `LoopRecord`;
- the MIR-to-EVM-IR `Stage` and the assembler's `checkL`. The driver proves these for every
  program, loop-free or not, as `ShapeGeneric.compiled_of` takes them.

```lean
namespace Verify.LoopSource.Equiv

structure Cut where
  fn : Nat                      -- the loop's function
  head : Nat                    -- its header block
  ids : List (Nat × Slot)       -- the template's values
  mem : List (Nat × Slot)       -- the template's memory words, at their offsets
  writes : List (WExpr × Slot)  -- the template's storage writes, newest first
  nhw : Nat                     -- the number of header words
  cases : List Facts            -- the facts each iteration run is under
  fuel : Nat

inductive Slot where | hw (k : Nat) | fixed (e : WExpr)
inductive Out where | exit (T : Tree) | back (hs : List WExpr)

def Cut.check (C : Cut) (ev : EnvFlags) (m : Module) (sel n : Nat) :
    Option (List (Facts × Out) × List (Facts × Out))

def nextVal (n : Nat) (σ : Val) (hs : List WExpr) : Val :=
  { σ with args := σ.args.take n ++ hs.map (·.eval σ) }
def trunc (n : Nat) (σ : Val) : Val := { σ with args := σ.args.take n }

structure Obl (L : Val → LoopRecord) (toSrc : Val → Val) (X : Val → Prop) (A : Val → Prop) (n : Nat)
    (cases : List Facts) (T : Tree) (le li : List (Facts × Out)) : Prop where
  entry : ∀ ρ : Val, ρ.args.length = n → ρ.Ok → A ρ → ∀ p ∈ le, p.1.Hold ρ →
    match p.2 with
    | .exit T' => (T'.eval ρ).obs = (T.eval ρ).obs
    | .back hs => (L ρ).P (toSrc (nextVal n ρ hs)) ∧ X (nextVal n ρ hs)
  iter : ∀ σ : Val, n ≤ σ.args.length → σ.Ok → A (trunc n σ) → (L (trunc n σ)).P (toSrc σ) → X σ →
    ∀ p ∈ li, p.1.Hold σ →
    match p.2 with
    | .exit T' => (T'.eval σ).obs = (T.eval (trunc n σ)).obs
    | .back hs => (L (trunc n σ)).Step (toSrc σ) (toSrc (nextVal n σ hs)) ∧ X (nextVal n σ hs)
  facts : ∀ σ : Val, n ≤ σ.args.length → σ.Ok → A (trunc n σ) → (L (trunc n σ)).P (toSrc σ) → X σ →
    ∃ F ∈ cases, F.Hold σ

theorem loop_mir_runs {C : Cut} {ev : EnvFlags} {m : Module} {sel n : Nat} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel n = some (le, li)) {L : Val → LoopRecord} {toSrc : Val → Val}
    {X A : Val → Prop} {T : Tree} (hobl : Obl L toSrc X A n C.cases T le li) {ρ : Val} {call : Call}
    (hc : CallFactsAt (.w (.lit 0)) sel n ρ call) (hlen : ρ.args.length = n) (hA : A ρ) (o : Oracle)
    (henv : EnvAsk ev o ρ) :
    (moduleSem o).run m call = some (T.eval ρ).obs

theorem loop_stage {fuel : Nat} {c : CheckedContract} {sel : Nat} {fn : FunctionDef} {ws : List Nat}
    {b : Br} {T : Tree} (hsel : sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? sel = some fn)
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    (hT : brTree fn (argFacts ws 0) b = some T)
    {C : Cut} {ev : EnvFlags} {m : Module} {le li : List (Facts × Out)}
    (hchk : C.check ev m sel fn.params.length = some (le, li))
    {L : Val → LoopRecord} {toSrc : Val → Val} {X A : Val → Prop}
    (hobl : Obl L toSrc X A fn.params.length C.cases T le li)
    (hA : ∀ σ args, ArgsOk fn ws args → A ⟨args, slotValue σ, solHash, callerWord⟩)
    (o : Oracle) (ho : SourceAsk ev o) :
    Stage (solidCoreRuntime fuel) (mirSem o) c m (SelCall sel fn ws)

theorem loop_equiv … (the premises of loop_stage, then)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert} {mx : List Nat}
    (backend : Stage (mirSem Shapes.oracle) (evmirSem Shapes.oracle) m q scope)
    (hscope : ∀ call, SelCall sel fn ws call → scope call)
    (asm : AssembleLoop.checkL q code cert mx = true) :
    Shapes.Equiv (solidCoreRuntime fuel) c code (SelCall sel fn ws)
end Verify.LoopSource.Equiv
```

`Cut.check` runs the module symbolically twice. The entry run goes from the module's entry; each
iteration run goes from the template after the header's phis, under one case. Both stop at every end
or arrival at the header. An arrival must hold the template: every fixed word is its word, header
words are read off, and nothing outside the template is written. A branch the case decides follows
its one side. `tools/certify/loop_equiv.py` in solar emits `C` from solar-verify's loop-head
manifest and solar's exported lowered MIR. The emitted `C` is a claim only: the kernel's check
rejects a wrong one.

## Loop-obligation generator (`Verify/LoopSource/Equiv/GenObl.lean`)

`Verify.LoopSource.Equiv.GenObl.run (cfg : Config) : IO UInt32`, run by the certify driver as
`lake env lean --run Certified/<name>/Loops/<fn>/Gen.lean`. `Config`: `stage0`, `stage0Name`, `cut`,
`cutName`, `contract?`, `contractName`, `sel`, `nargs`, `imports`, `pre`, `ns`, `root`, `files`, and
`body? : Option Br := none` with `bodyName : String := ""`, the loop route's summary of the function's
body (the source erasure has no loop case; without it `run` refuses). It writes
`<root>/<pre>{Data,V0..Vk,Obl}.lean` with `leaves`, `tree` (by `kernel_rfl`), `seqs`, `valid` and `obl`
in `ns`, prints `{"format":"loop obligations 1","modules":[…],"measure":"…"}` and returns 0, or
returns 2 with the reason on stderr.

The iteration-bound premise for Counter's resources is `CounterGas.BumpCallBounded K` with its
witness `CounterGas.bounded_inhabited` (`Counter/Gas.lean`); `Shapes.Resources` under it is OPEN.
