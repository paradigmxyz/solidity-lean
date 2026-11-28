import Verify.Spec.Contract
import Verify.ShapeSpecExportTac
import Verify.Generic.CtorWords

/-!
# The constructor's exported spec on the storage a creation leaves

`CtorMeets b ctx ws σ`: the exported contract's constructor spec (`b.spec.ctor`) exists, its ensures are not
empty, its parameters decode the argument words `ws` and its requires hold there (so the premise is
satisfiable), and from every decoding whose requires hold, its ensures **and the contract invariants**
hold in the post-creation state whose storage is `slotValue σ`: the exact storage the creation leaves,
not an arbitrary cover of its keys. Ghost state starts at zero (`Ghost.zero`) and the time is the block's.

`ctor_meets [defs]` proves it for a concrete export and a storage list over the argument words, by
evaluating the terms; `CtorMeets.inv` reads the invariants off it, `not_ctorMeets_none` shows an
export without a constructor spec never meets it (no vacuous `True`).
-/

namespace SolidCore.Spec

/-- The constructor spec's environment: its argument values, in the post-creation state `post`. -/
def ctorEnv (ctx : Ctx) (args : List Int) (post : State) : Env := mkEnv ctx args [] post post

/-- The post-creation state on the storage list `σ`: its slots, no ghost update, the block's time. -/
def ctorPost (ctx : Ctx) (σ : List (Nat × Nat)) : State := ⟨SolarTV.slotValue σ, Ghost.zero, ctx.timestamp⟩

/-- **The constructor's exported spec holds of the storage `σ` the creation leaves on `ws`.** -/
def CtorMeets (b : Bundle) (ctx : Ctx) (ws : List Nat) (σ : List (Nat × Nat)) : Prop :=
  ∃ cs, b.spec.ctor = some cs ∧ cs.ensures ≠ [] ∧
    (∃ args, decodeWords cs.params ws = some args ∧ b.satAll cs.requires (ctorEnv ctx args (ctorPost ctx σ))) ∧
    ∀ args, decodeWords cs.params ws = some args →
      b.satAll cs.requires (ctorEnv ctx args (ctorPost ctx σ)) →
      b.satAll cs.ensures (ctorEnv ctx args (ctorPost ctx σ)) ∧
        b.satAll b.spec.invariants (ctorEnv ctx args (ctorPost ctx σ))

/-- The invariants on the post-creation storage, from `CtorMeets`. -/
theorem CtorMeets.inv {b : Bundle} {ctx : Ctx} {ws : List Nat} {σ : List (Nat × Nat)}
    (h : CtorMeets b ctx ws σ) :
    ∃ args, b.satAll b.spec.invariants (ctorEnv ctx args (ctorPost ctx σ)) := by
  obtain ⟨cs, -, -, ⟨args, hd, hr⟩, hall⟩ := h
  exact ⟨args, (hall args hd hr).2⟩

/-- An export without a constructor spec never meets `CtorMeets`. -/
theorem not_ctorMeets_none {b : Bundle} (h : b.spec.ctor = none) (ctx : Ctx) (ws : List Nat)
    (σ : List (Nat × Nat)) : ¬ CtorMeets b ctx ws σ := by
  rintro ⟨cs, hc, -⟩
  rw [h] at hc
  cases hc

/-- `ctor_meets [defs] hA args`: `CtorMeets b ctx ws σ` for a concrete export `b` (with `defs` unfolding it and
the storage list), argument words `ws` bounded by `hA`, and `args` their decoding: the spec is found by
evaluation, the words decode to `args`, and each requires, ensures and invariant is evaluated on the
storage and closed by `omega`. -/
macro "ctor_meets" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" h:term:max a:term:max : tactic => `(tactic| (
  have hlt := $h
  simp only [Nat.reducePow] at hlt
  refine ⟨_, rfl, by simp [$ds,*], ⟨$a, ?_, ?_⟩, ?_⟩
  · simp [$ds,*, decodeWords, Ty.ofWord, hlt]
  · simp [Bundle.satAll, Bundle.sat, $ds,*, eval, slotOf, ctorEnv, ctorPost, mkEnv, Env.cur, BinOp.apply,
      Ty.ofBits, toWord, ofProp, SolarTV.slotValue, SolidCore.Refinement.Generic.storageOf,
      SolidCore.Refinement.Generic.WExpr.eval, SolidCore.Refinement.Generic.wordSize, wordMod] <;> omega
  · intro args hd _
    simp only [$ds,*, decodeWords, Ty.ofWord, bind, pure, Option.bind, Nat.reducePow] at hd
    split_ifs at hd <;> (try simp only [Option.some.injEq, reduceCtorEq] at hd) <;> (try omega)
    subst hd
    simp [Bundle.satAll, Bundle.sat, $ds,*, eval, slotOf, ctorEnv, ctorPost, mkEnv, Env.cur, BinOp.apply,
      Ty.ofBits, toWord, ofProp, SolarTV.slotValue, SolidCore.Refinement.Generic.storageOf,
      SolidCore.Refinement.Generic.WExpr.eval, SolidCore.Refinement.Generic.wordSize, wordMod] <;> omega))

end SolidCore.Spec
