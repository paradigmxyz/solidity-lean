import Verify.Basic
import Std.WP
import Std.Tactic.Do

/-!
# Lane D: `SolM`'s weakest preconditions through Lean's `Std.WP` and `Std.Do`

`SolM` is `StateT Storage (Except Revert)`, so Lean's own frameworks already interpret it:
`Std.WP` (the lattice framework `vcgen` runs on) with assertions `Storage → Prop` and
exception postconditions `Revert → Prop`, and `Std.Do` (the framework of the deprecated
`mvcgen`) with post shape `.arg Storage (.except Revert .pure)`. No instance is added here.

`loom_wp_eq_stdWP` says that Loom's weakest precondition of a model, the one every `vc`,
`Triple` and `Implements` theorem of `Verify.Basic` is stated with, is `Std.WP`'s for the
same postcondition, with Loom's revert predicate as the exception postcondition; so a `vcgen`
proof of a `Std.WP` triple closes a Loom goal unchanged, and no new trusted model is introduced:
both sides unfold to the same `match` on the model's outcome (`Verify.wp_eq`). The rules for the
model's primitives (`sload`, `sstore`, `revert`) and the bounded loop `whileM` are proved here
as `Std.WP` specifications from their definitions and from Loom's loop rule `triple_whileM`.
-/

namespace SolidCore.Verify.Eval.D

open SolidCore.Verify SolidCore.Refinement
open Lean.Order
open scoped Std.WP

/-! ## The bridge -/

/-- Loom's weakest precondition of a `SolM` program is `Std.WP`'s. -/
theorem loom_wp_eq_stdWP {α : Type} (x : SolM α) (post : α → Assn) (herr : Revert → Prop)
    (s : Storage) :
    wp x post herr s = Std.WP.wp x (fun a s' => post a herr s') herr s := by
  rw [wp_eq, Std.WP.StateT.wp_apply_eq]
  rcases h : x s with e | ⟨a, s'⟩ <;> simp [StateT.run, h] <;> rfl

/-- A `Std.WP` triple from the initial storage proves Loom's weakest precondition. -/
theorem loom_wp_of_triple {α : Type} {x : SolM α} {post : α → Assn} {herr : Revert → Prop}
    {s : Storage}
    (h : Std.WP.Triple x (fun s' => s' = s) (fun a s' => post a herr s') herr) :
    wp x post herr s := by
  rw [loom_wp_eq_stdWP]; exact h.le_wp s rfl

/-- The same with the initial storage given pointwise, the form `grind` instantiates. -/
theorem loom_wp_of_triple_pt {α : Type} {x : SolM α} {post : α → Assn} {herr : Revert → Prop}
    {s : Storage}
    (h : Std.WP.Triple x (fun s' => ∀ k, s' k = s k) (fun a s' => post a herr s') herr) :
    wp x post herr s := by
  rw [loom_wp_eq_stdWP]; exact h.le_wp s (fun _ => rfl)

/-- Loom's `vc` of a model, as a `Std.WP` triple from the call's initial storage. -/
theorem vc_of_triple {model : List Nat → SolM (List Nat)} {args : Call → List Nat}
    {post : Call → Observable → Prop} {call : Call}
    (h : Std.WP.Triple (model (args call)) (fun s' => s' = initStorage call)
      (fun out s' => post call { success := true, output := out, logs := [], storage := s' })
      (fun e => post call { success := false, output := e, logs := [], storage := initStorage call })) :
    vc model args post call :=
  loom_wp_of_triple h

/-- The same bridge to `Std.Do` (the post shape `mvcgen` works with). -/
theorem loom_wp_iff_stdDo {α : Type} (x : SolM α) (post : α → Assn) (herr : Revert → Prop)
    (s : Storage) :
    wp x post herr s ↔
      (Std.Do.PredTrans.apply (Std.Do.WP.wp x)
        ((fun a s' => ULift.up (post a herr s'), fun e => ULift.up (herr e), ()) :
          Std.Do.PostCond α (.arg Storage (.except Revert .pure))) s).down := by
  rw [wp_eq]
  rcases h : x s with e | ⟨a, s'⟩ <;>
    simp [Std.Do.WP.wp, Std.Do.PredTrans.pushArg, Std.Do.PredTrans.apply, StateT.run, h] <;> rfl

theorem loom_wp_of_stdDo_triple {α : Type} {x : SolM α} {post : α → Assn}
    {herr : Revert → Prop} {s : Storage}
    (h : Std.Do.Triple x (fun s' => ULift.up (s' = s))
      ((fun a s' => ULift.up (post a herr s'), fun e => ULift.up (herr e), ()) :
        Std.Do.PostCond α (.arg Storage (.except Revert .pure)))) :
    wp x post herr s :=
  (loom_wp_iff_stdDo x post herr s).mpr (h s rfl)

theorem loom_wp_of_stdDo_triple_pt {α : Type} {x : SolM α} {post : α → Assn}
    {herr : Revert → Prop} {s : Storage}
    (h : Std.Do.Triple x (fun s' => ULift.up (∀ k, s' k = s k))
      ((fun a s' => ULift.up (post a herr s'), fun e => ULift.up (herr e), ()) :
        Std.Do.PostCond α (.arg Storage (.except Revert .pure)))) :
    wp x post herr s :=
  (loom_wp_iff_stdDo x post herr s).mpr (h s (fun _ => rfl))

/-! ## `Std.WP` specifications of the model's primitives -/

@[spec] theorem sload_spec (slot : Nat) (post : Nat → Storage → Prop) (e : Revert → Prop) :
    Std.WP.Triple (sload slot) (fun s => post (s slot) s) post e := ⟨fun _ h => h⟩

@[spec] theorem sstore_spec (slot v : Nat) (post : Unit → Storage → Prop) (e : Revert → Prop) :
    Std.WP.Triple (sstore slot v)
      (fun s => post () (fun k => if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else s k))
      post e := ⟨fun _ h => h⟩

@[spec] theorem revert_spec {α : Type} (data : Revert) (post : α → Storage → Prop)
    (e : Revert → Prop) :
    Std.WP.Triple (revert data : SolM α) (fun _ => e data) post e := ⟨fun _ h => h⟩

/-! ## `Std.Do` specifications of the model's primitives (for `mvcgen`) -/

@[spec] theorem sload_spec_do (slot : Nat)
    (Q : Std.Do.PostCond Nat (.arg Storage (.except Revert .pure))) :
    Std.Do.Triple (sload slot) (fun s => Q.1 (s slot) s) Q := fun _ h => h

@[spec] theorem sstore_spec_do (slot v : Nat)
    (Q : Std.Do.PostCond Unit (.arg Storage (.except Revert .pure))) :
    Std.Do.Triple (sstore slot v)
      (fun s => Q.1 () (fun k => if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else s k)) Q :=
  fun _ h => h

@[spec] theorem revert_spec_do {α : Type} (data : Revert)
    (Q : Std.Do.PostCond α (.arg Storage (.except Revert .pure))) :
    Std.Do.Triple (revert data : SolM α) (fun _ => Q.2.1 data) Q := fun _ h => h

/-! ## The bounded loop, from an invariant and a variant supplied from outside

`whileM` is Loom's `Loop.whileBounded` with an exhausting branch that reverts. The rule below is
Loom's `triple_whileM` restated as a `Std.WP` triple: the invariant and the variant are explicit
arguments, so they come from an annotation, a Spacer model or any other source; the generator
only checks them (establishment is the precondition, preservation and the decreasing variant are
`hbody`, exit is the postcondition, and `hfuel` shows the fuel never runs out). Nothing unrolls
the loop. -/

/-- Loom's weakest precondition is monotone in the postcondition at one revert predicate. -/
theorem wp_mono_at {α : Type} {x : SolM α} {P Q : α → Assn} {herr : Revert → Prop} {s : Storage}
    (hPQ : ∀ a s', P a herr s' → Q a herr s') (h : wp x P herr s) : wp x Q herr s := by
  rw [wp_eq] at h ⊢
  rcases hx : x s with r | ⟨a, s'⟩ <;> simp only [hx] at h ⊢
  · exact h
  · exact hPQ a s' h

theorem whileM_spec {β : Type} (cond : β → Bool) (body : β → SolM β) (fuel : Nat) (init : β)
    (inv : β → Storage → Prop) (measure : β → Nat) (e : Revert → Prop)
    (hbody : ∀ b, cond b = true →
      Std.WP.Triple (body b) (inv b) (fun b' s => inv b' s ∧ measure b' < measure b) e)
    (hfuel : measure init < fuel) :
    Std.WP.Triple (whileM cond body fuel init) (inv init)
      (fun b s => inv b s ∧ cond b = false) e := by
  refine ⟨fun s hs => ?_⟩
  let I : β → Assn := fun b herr s => herr = e ∧ inv b s
  have hloom := triple_whileM cond body I measure ?step fuel init hfuel e s ⟨rfl, hs⟩
  case step =>
    intro b hb herr s ⟨he, hi⟩
    subst he
    have h1 := (hbody b hb).le_wp s hi
    rw [← loom_wp_eq_stdWP (body b) (fun b' _ s => inv b' s ∧ measure b' < measure b)] at h1
    refine wp_mono_at (fun b' s' ⟨hi', hlt⟩ => ?_) h1
    exact ⟨⟨rfl, hi'⟩, by simp [LE.pure, hlt]⟩
  have h2 : wp (whileM cond body fuel init) (fun b (_ : Revert → Prop) s => inv b s ∧ cond b = false) e s := by
    refine wp_mono_at (fun b s' ⟨⟨_, hi⟩, hc⟩ => ⟨hi, ?_⟩) hloom
    by_contra hne
    simp [LE.pure, hne] at hc
  rw [loom_wp_eq_stdWP] at h2
  exact h2

end SolidCore.Verify.Eval.D
