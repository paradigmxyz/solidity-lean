import Verify.Spec.Semantics

/-!
# A function's spec over a call and its observable

`Pre` and `Post` are a function's spec as predicates over a `SolarTV.Call` and the
`SolarTV.Observable` it finishes with, given the call's environment (`Ctx`), the ghost state before
and after it and `__time` before it. `Holds` says that every function's spec holds of a program in
a semantics. Because SolidCore (`SolidCore.Refinement.solidCore`) and EthLib
(`SolidCore.Refinement.ethLib`) are both `SolarTV.Sem`s over the same calls and observables, the
same `Holds` states the spec of the source and of the bytecode, and a refinement between them
carries one to the other (`Holds.of_stage`).

The meaning follows solar-verify's (crates/verify/README.md, "Semantics"):

* the requires and the contract invariants are assumed of the pre-state, with `__time` the time
  before the call, at most the block's timestamp;
* a successful call returns ABI-clean words of the return types, and the ensures and the
  invariants hold of the post-state, in which `__time` is the block's timestamp;
* a reverted call owes nothing, since it has no effect (the semantics' failure convention);
* from a pre-state meeting the succeeds-if conditions (and the requires), the call succeeds.
-/

namespace SolidCore.Spec

open SolarTV

/-- The 32-byte big-endian words of a byte list (a short last word is dropped). -/
def words (bs : List Nat) : List Nat :=
  (List.range (bs.length / 32)).map fun i => bytesWord ((bs.drop (32 * i)).take 32)

/-- Decode words as values of the types, or `none` when there are too few or one is not clean. -/
def decodeWords : List Ty → List Nat → Option (List Int)
  | [], _ => some []
  | _ :: _, [] => none
  | t :: ts, w :: ws => do
    let v ← t.ofWord w
    let vs ← decodeWords ts ws
    pure (v :: vs)

/-- The selector of a call: its first four bytes. -/
def selectorOf (call : Call) : Nat := bytesWord ((call.calldata.data.toList.map (·.toNat)).take 4)

/-- The call is to `fs`, with arguments `args`: the selector matches and the argument words are
clean for the parameter types. -/
def Decodes (fs : FnSpec) (call : Call) (args : List Int) : Prop :=
  4 ≤ call.calldata.size ∧ selectorOf call = fs.selector ∧
    decodeWords fs.params (words ((call.calldata.data.toList.map (·.toNat)).drop 4)) = some args

/-- The environment of a spec expression on a call. -/
def mkEnv (ctx : Ctx) (args rets : List Int) (pre post : State) : Env :=
  { args, rets, pre, post, ctx, vars := [], inOld := false }

/-- The spec of a contract's functions, with `fuel` the bound on nested spec function calls. -/
structure Bundle where
  spec : ContractSpec
  fuel : Nat

/-- A formula of the bundle holds in an environment. -/
def Bundle.sat (b : Bundle) (t : Term) (e : Env) : Prop := eval b.spec.fns b.fuel t e ≠ 0

/-- Every formula of a list holds. -/
def Bundle.satAll (b : Bundle) (ts : List Term) (e : Env) : Prop := ∀ t ∈ ts, b.sat t e

/-- The precondition of `fs` on `call` from the state `pre`: the arguments decode, `pre` is the
call's storage, `__time` is at most the block's timestamp, and the requires and invariants hold. -/
def Pre (b : Bundle) (fs : FnSpec) (ctx : Ctx) (pre : State) (call : Call) (args : List Int) :
    Prop :=
  Decodes fs call args ∧ pre.storage = slotValue call.storage ∧ pre.time ≤ ctx.timestamp ∧
    b.satAll fs.requires (mkEnv ctx args [] pre pre) ∧
    b.satAll b.spec.invariants (mkEnv ctx args [] pre pre)

/-- The postcondition of `fs` on `call` from `pre`, finishing with `obs` and the ghost state
`ghost'`: a success returns clean words meeting the ensures and leaves a state meeting the
invariants; when `fs` has succeeds-if conditions, from a pre-state meeting them the call
succeeds. A function without any makes no claim that it succeeds, as in solar-verify, whose
export then writes `succeedsIf := []`. -/
def Post (b : Bundle) (fs : FnSpec) (ctx : Ctx) (pre : State) (ghost' : Ghost) (obs : Observable)
    (args : List Int) : Prop :=
  let post : State := { storage := obs.storage, ghost := ghost', time := ctx.timestamp }
  (obs.success = true → ∃ rets, decodeWords fs.rets (words obs.output) = some rets ∧
    b.satAll fs.ensures (mkEnv ctx args rets pre post) ∧
    b.satAll b.spec.invariants (mkEnv ctx args rets post post)) ∧
  (fs.succeedsIf ≠ [] → b.satAll fs.succeedsIf (mkEnv ctx args [] pre pre) → obs.success = true)

/-- The ghost state after a call, from the call and the ghost state before it. -/
abbrev GhostStep := Call → Ghost → Ghost

/-- `fs`'s spec holds of `p` in `S` on `scope`: every call of the scope to `fs` from a pre-state
meeting `Pre` finishes, with an observable meeting `Post`. -/
def HoldsFn (S : Sem) (p : S.Prog) (scope : Call → Prop) (b : Bundle) (ctxOf : Call → Ctx)
    (step : GhostStep) (fs : FnSpec) : Prop :=
  ∀ call, scope call → ∀ (args : List Int) (pre : State), Pre b fs (ctxOf call) pre call args →
    ∃ obs, S.run p call = some obs ∧ Post b fs (ctxOf call) pre (step call pre.ghost) obs args

/-- Every function's spec holds of `p`. -/
def Holds (S : Sem) (p : S.Prog) (scope : Call → Prop) (b : Bundle) (ctxOf : Call → Ctx)
    (step : GhostStep) : Prop :=
  ∀ fs ∈ b.spec.specs, HoldsFn S p scope b ctxOf step fs

/-- A refinement carries a spec from source to target: a stage from `S` to `T` preserves every
observable `p` finishes with, and `Post` speaks only of the observable. -/
theorem HoldsFn.of_stage {S T : Sem} {p : S.Prog} {q : T.Prog} {scope : Call → Prop}
    {b : Bundle} {ctxOf : Call → Ctx} {step : GhostStep} {fs : FnSpec}
    (h : HoldsFn S p scope b ctxOf step fs) (st : Stage S T p q scope) :
    HoldsFn T q scope b ctxOf step fs := by
  intro call hs args pre hpre
  obtain ⟨obs, hrun, hpost⟩ := h call hs args pre hpre
  exact ⟨obs, st call hs obs hrun, hpost⟩

theorem Holds.of_stage {S T : Sem} {p : S.Prog} {q : T.Prog} {scope : Call → Prop}
    {b : Bundle} {ctxOf : Call → Ctx} {step : GhostStep}
    (h : Holds S p scope b ctxOf step) (st : Stage S T p q scope) :
    Holds T q scope b ctxOf step :=
  fun fs hfs => (h fs hfs).of_stage st

/-- A spec holds on any narrower scope. -/
theorem HoldsFn.mono {S : Sem} {p : S.Prog} {scope narrower : Call → Prop} {b : Bundle}
    {ctxOf : Call → Ctx} {step : GhostStep} {fs : FnSpec} (h : HoldsFn S p scope b ctxOf step fs)
    (hn : ∀ call, narrower call → scope call) : HoldsFn S p narrower b ctxOf step fs :=
  fun call hc => h call (hn call hc)

/-! ## Checked obligations -/

/-- Every spec function call of the bundle resolves and nests within its fuel, and every spec
function's body does too. Computable: the kernel checks it of an exported bundle by `decide`. -/
def Bundle.WF (b : Bundle) : Bool :=
  (b.spec.specs.all fun fs =>
    Term.ClosedList b.spec.fns b.fuel fs.requires &&
    Term.ClosedList b.spec.fns b.fuel fs.ensures &&
    Term.ClosedList b.spec.fns b.fuel fs.succeedsIf) &&
  Term.ClosedList b.spec.fns b.fuel b.spec.invariants

/-- Every opaque spec function's body takes values in its return type's range, at every depth
up to the fuel and in every environment: the range solar-verify assumes of an opaque
application, so that its proofs, which hold for every function in that range, hold for this one. -/
def OpaqueInRange (b : Bundle) : Prop :=
  ∀ f ∈ b.spec.fns, f.isOpaque = true → ∀ k ≤ b.fuel, ∀ e, f.ret.InRange (eval b.spec.fns k f.body e)

theorem opaqueInRange_of_none {b : Bundle} (h : b.spec.fns.all (fun f => !f.isOpaque) = true) :
    OpaqueInRange b := by
  intro f hf ho
  have := List.all_eq_true.mp h f hf
  simp [ho] at this

/-! ## Ghost-free specs -/

mutual
/-- One level of `Term.GhostFree`: `t` reads no ghost variable, and `k` holds of the bodies of the
spec functions it calls. -/
def Term.ghostFreeWith (fns : List SpecFn) (k : Term → Bool) : Term → Bool
  | .ghost _ _ => false
  | .load p off _ _ => Place.ghostFreeWith fns k p && Term.ghostFreeWith fns k off
  | .len p => Place.ghostFreeWith fns k p
  | .old t | .un _ t | .shl t _ | .shr t _ | .all _ _ t | .ex _ _ t => Term.ghostFreeWith fns k t
  | .bin _ a b => Term.ghostFreeWith fns k a && Term.ghostFreeWith fns k b
  | .ite c a b => Term.ghostFreeWith fns k c && Term.ghostFreeWith fns k a && Term.ghostFreeWith fns k b
  | .call f args =>
    Term.ghostFreeListWith fns k args &&
    match fns.find? (·.name == f) with
    | some sf => k sf.body
    | none => true
  | .lit _ | .arg _ | .ret _ | .var _ | .env _ => true

def Term.ghostFreeListWith (fns : List SpecFn) (k : Term → Bool) : List Term → Bool
  | [] => true
  | t :: ts => Term.ghostFreeWith fns k t && Term.ghostFreeListWith fns k ts

def Place.ghostFreeWith (fns : List SpecFn) (k : Term → Bool) : Place → Bool
  | .slot _ => true
  | .offset b i | .entry b i | .elem b i _ | .packedElem b i _ =>
    Place.ghostFreeWith fns k b && Term.ghostFreeWith fns k i
end

/-- `t` reads no ghost variable, through spec function calls nested at most `fuel` deep. -/
def Term.GhostFree (fns : List SpecFn) : Nat → Term → Bool
  | 0 => Term.ghostFreeWith fns fun _ => true
  | n + 1 => Term.ghostFreeWith fns (Term.GhostFree fns n)

/-- Two environments that differ only in their ghost states. -/
def Env.ghostEquiv (e e' : Env) : Prop :=
  e.args = e'.args ∧ e.rets = e'.rets ∧ e.ctx = e'.ctx ∧ e.vars = e'.vars ∧ e.inOld = e'.inOld ∧
    e.pre.storage = e'.pre.storage ∧ e.pre.time = e'.pre.time ∧
    e.post.storage = e'.post.storage ∧ e.post.time = e'.post.time

end SolidCore.Spec
