import Loom.MonadAlgebras.WP.Basic
import SolidCore.Refinement.Compose

/-!
# A verification-condition generator for SolidCore, on Loom

A specification of an external function says what a call must show, from what holds
before it. Its triple (`Triple`) is stated directly against SolidCore's
`Source.run`: every call of the scope that meets the precondition finishes with some
observable, and every observable it can finish with meets the postcondition.

The verification conditions come from Loom's weakest preconditions. A function is
modelled as a program in `SolM`, a state monad over the callee's storage whose
failures are reverts with their revert data. `SolM` is a Loom ordered monad algebra
(`MAlgOrdered`) whose assertions take, besides the storage, a predicate on the revert
data a failure must meet, so that one weakest precondition covers both outcomes of a
call. Loom's `wp_bind` and `wp_pure` and the rules below for storage and reverts
compute the weakest precondition of a model by `simp`; what is left is a goal on words
that `omega` or `bv_decide` closes.

A model is tied to SolidCore by `Implements`: on every call of the scope,
`Source.run` finishes with the observable the model's outcome shows. Each contract
proves it once, by symbolic evaluation of SolidCore's interpreter (`Wide.Tactic`).
`triple_of_wp` then turns the weakest precondition into the triple, and
`satisfies_of_triple` into `Satisfies` on `solidCore fuel`, the form the refinement
theorems carry to bytecode.

The triple is total: it includes that `Source.run` returns `some`, so running out
of fuel or an interpreter failure refutes it.
-/

namespace SolidCore.Verify

open SolidCore.Refinement

/-- The callee's storage, slot to word. -/
abbrev Storage := Nat → Nat

/-- The data a call reverts with. -/
abbrev Revert := List Nat

/-- A model of an external function: a program over the storage that fails with its
revert data. -/
abbrev SolM := StateT Storage (Except Revert)

/-- An assertion on what a model leaves: given the predicate a revert's data must meet,
a predicate on the storage. -/
abbrev Assn := (Revert → Prop) → Storage → Prop

/-- What a model's outcome means for an assertion: a result's assertion at its final
storage, or the revert predicate on the revert data. -/
def Assn.ofOutcome : Except Revert (Assn × Storage) → (Revert → Prop) → Prop
  | .ok (p, s'), herr => p herr s'
  | .error e, herr => herr e

/-- `SolM` is a Loom ordered monad algebra on `Assn`. -/
instance : MAlgOrdered SolM Assn where
  μ x := fun herr s => Assn.ofOutcome (x s) herr
  μ_ord_pure := by intro l; rfl
  μ_ord_bind := by
    intro α f g h x herr s
    show Assn.ofOutcome ((x s).bind fun a => f a.1 a.2) herr →
      Assn.ofOutcome ((x s).bind fun a => g a.1 a.2) herr
    rcases x s with e | ⟨a, s'⟩
    · exact id
    · exact h a herr s'

/-! ## Weakest preconditions of the model's primitives -/

theorem wp_eq (x : SolM α) (post : α → Assn) :
    wp x post = fun herr s => match x s with
      | .ok (a, s') => post a herr s'
      | .error e => herr e := by
  funext herr s
  show Assn.ofOutcome ((post <$> x) s) herr = _
  simp only [Functor.map, StateT.map]
  rcases h : x s with e | ⟨a, s'⟩ <;> simp [h, Assn.ofOutcome, bind, Except.bind, pure, Except.pure]

/-- Read a storage slot. -/
def sload (slot : Nat) : SolM Nat := fun s => .ok (s slot, s)

/-- Write a storage slot. Slots and values are 256-bit words, as in `slotValue` and
SolidCore's storage: a write to `slot` is a write to every slot equal to it modulo
`2 ^ 256`. -/
def sstore (slot v : Nat) : SolM Unit :=
  fun s => .ok ((), fun k => if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else s k)

/-- Revert with `data`. -/
def revert (data : Revert) : SolM α := fun _ => .error data

@[simp] theorem wp_sload (slot : Nat) (post : Nat → Assn) :
    wp (sload slot) post = fun herr s => post (s slot) herr s := by
  rw [wp_eq]; rfl

@[simp] theorem wp_sstore (slot v : Nat) (post : Unit → Assn) :
    wp (sstore slot v) post = fun herr s =>
      post () herr (fun k => if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else s k) := by
  rw [wp_eq]; rfl

@[simp] theorem wp_revert (data : Revert) (post : α → Assn) :
    wp (revert data : SolM α) post = fun herr _ => herr data := by
  rw [wp_eq]; rfl

@[simp] theorem wp_ite (c : Prop) [Decidable c] (x y : SolM α) (post : α → Assn) :
    wp (if c then x else y) post = if c then wp x post else wp y post := by
  split <;> rfl

/-! ## Models, triples and the generator -/

/-- The observable of a model's outcome, from the initial storage `s`: a returned word
list and the final storage, or a revert with its data and the initial storage. A model
emits no logs. -/
def observe (s : Storage) : Except Revert (List Nat × Storage) → Observable
  | .ok (out, s') => { success := true, output := out, logs := [], storage := s' }
  | .error e => { success := false, output := e, logs := [], storage := s }

/-- The storage a call starts from, as a function. -/
def initStorage (call : Call) : Storage := slotValue call.storage

/-- `model` implements `contract` on `scope`: on every call of it, SolidCore with `fuel`
finishes with the observable of the model on the call's argument words `args call`. -/
def Implements (fuel : Nat) (contract : SolidCore.Solidity.TypeCheck.CheckedContract)
    (scope : Call → Prop) (args : Call → List Nat) (model : List Nat → SolM (List Nat)) : Prop :=
  ∀ call, scope call →
    Source.run fuel contract call = some (observe (initStorage call) (model (args call) (initStorage call)))

/-- The triple `{pre} contract {post}` on `scope`, against SolidCore: every call of the
scope that meets `pre` finishes, and every observable it finishes with meets `post`. -/
def Triple (fuel : Nat) (contract : SolidCore.Solidity.TypeCheck.CheckedContract)
    (scope : Call → Prop) (pre : Call → Prop) (post : Call → Observable → Prop) : Prop :=
  ∀ call, scope call → pre call →
    (Source.run fuel contract call).isSome ∧
      ∀ obs, Source.run fuel contract call = some obs → post call obs

/-- Total correctness of `p` in `S` on `scope`: every call that meets `pre` finishes with an
observable that meets `post`. The same statement as the refinement's `Satisfies`. -/
def Satisfies (S : Sem) (p : S.Prog) (scope : Call → Prop) (pre : Call → Prop)
    (post : Call → Observable → Prop) : Prop :=
  ∀ call, scope call → pre call → ∃ obs, S.run p call = some obs ∧ post call obs

/-- The verification condition of a model: Loom's weakest precondition of the model on
the call's argument words, for the postcondition on a success and on a revert, at the
call's initial storage. -/
def vc (model : List Nat → SolM (List Nat)) (args : Call → List Nat)
    (post : Call → Observable → Prop) (call : Call) : Prop :=
  wp (model (args call))
    (fun out _ s' => post call { success := true, output := out, logs := [], storage := s' })
    (fun e => post call { success := false, output := e, logs := [], storage := initStorage call })
    (initStorage call)

/-- The generator's soundness: a model that implements the contract and whose
verification condition holds under the precondition gives the triple. -/
theorem triple_of_wp {fuel : Nat} {contract : SolidCore.Solidity.TypeCheck.CheckedContract}
    {scope : Call → Prop} {args : Call → List Nat} {model : List Nat → SolM (List Nat)}
    {pre : Call → Prop} {post : Call → Observable → Prop}
    (himpl : Implements fuel contract scope args model)
    (hvc : ∀ call, scope call → pre call → vc model args post call) :
    Triple fuel contract scope pre post := by
  intro call hs hp
  have hrun := himpl call hs
  have h := hvc call hs hp
  simp only [vc, wp_eq] at h
  refine ⟨by simp [hrun], fun obs hobs => ?_⟩
  rw [hrun] at hobs
  cases hobs
  revert h
  rcases model (args call) (initStorage call) with e | ⟨out, s'⟩ <;> exact id

theorem satisfies_iff_triple {fuel : Nat} {contract : SolidCore.Solidity.TypeCheck.CheckedContract}
    {scope pre : Call → Prop} {post : Call → Observable → Prop} :
    Satisfies (solidCore fuel) contract scope pre post ↔ Triple fuel contract scope pre post := by
  constructor
  · intro h call hs hp
    obtain ⟨obs, hrun, hpost⟩ := h call hs hp
    exact ⟨by simp [solidCore] at hrun; simp [hrun], fun o ho => by
      simp [solidCore] at hrun; rw [hrun] at ho; cases ho; exact hpost⟩
  · intro h call hs hp
    obtain ⟨hsome, hpost⟩ := h call hs hp
    obtain ⟨obs, hobs⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨obs, hobs, hpost obs hobs⟩

theorem satisfies_of_triple {fuel : Nat} {contract : SolidCore.Solidity.TypeCheck.CheckedContract}
    {scope pre : Call → Prop} {post : Call → Observable → Prop}
    (h : Triple fuel contract scope pre post) :
    Satisfies (solidCore fuel) contract scope pre post :=
  satisfies_iff_triple.mpr h

end SolidCore.Verify

