import Contracts.Counter.VC.Inc

/-!
# The certified counter milestone's `get`

`get` carries no NatSpec clause, so solar-verify emits no obligation for it and there is nothing of
solar-verify's to bind: `get_triple` is `triple_of_binds` with no obligation, with the shape of
`inc_triple` so that final composition consumes both the same way.

* `getShape_eq` (kernel): `Counter` deploys with no storage and no logs, and the generic source stage
  erases `get()` to `getTree`, one success leaf that returns slot 0's 32 bytes and writes nothing.
* `get_triple`: on the stage's scope (any storage, no value), `get` succeeds, returns slot 0 as a
  big-endian word and leaves every slot unchanged.
-/

namespace SolidCore.Verify.VC.Counter

open SolidCore.Verify SolidCore.Verify.VC SolidCore.Refinement SolidCore.Refinement.Abi
open SolidCore.Refinement.Generic SolidCore.Solidity SolidCore.Solidity.Source

/-- `get()` as the stage's ABI sees it. -/
def fnGet : Fn := ⟨getSel, []⟩

/-- The erasure of `get`: return slot 0's word, write nothing. -/
def getTree : Tree := .halt true (wordOBytes (.init 0)) [] []

/-- Whether `Counter` deploys with no storage and no logs, and how SolidCore dispatches `get` and the
generic source stage erases it. -/
def getShape? : Option (Bool × Option (Nat × Option Tree)) :=
  match contract? with
  | .ok c => some (Wide.deployedAt fuel c [],
      (c.core.findFunctionBySelector? getSel).map fun f => (f.params.length, eraseFn (envOf c.core) fuel f))
  | .error _ => none

kernel_rfl getShape_eq getShape? (some (true, some (0, some getTree))) using selector_eq mkIdx_eq

/-- The 32 bytes of the word `w`, big-endian. -/
def wordBytes (w : Nat) : List Nat := (List.range 32).map fun i => w / 256 ^ (31 - i) % 256

/-- `get`'s postcondition: it succeeds, returns slot 0 as a big-endian word and changes no slot. -/
def getPost (call : Call) (obs : SolarTV.Observable) : Prop :=
  let s := initStorage call
  obs.success = true ∧ obs.output = wordBytes (s 0) ∧ ∀ k, obs.storage k = s k

/-- `getPost` of a call's storage. -/
def getP (_ : List Nat) (s : Storage) (o : SolarTV.Observable) : Prop :=
  o.success = true ∧ o.output = wordBytes (s 0) ∧ ∀ k, o.storage k = s k

/-- `get`'s erased tree returns slot 0's word and writes nothing; there is no obligation. -/
theorem get_binds : Binds fnGet getTree [] (fun _ s => incEnv 0 s) getP := by
  rintro args s - - hs -
  simp only [getP]
  refine ⟨rfl, ?_, fun k => rfl⟩
  simp only [Res.obs, getTree, Tree.eval, wordOBytes, wordBytes, List.map_map]
  congr 1
  funext i
  simp only [Function.comp_apply, OByte.eval, WExpr.eval, valOf, Generic.wordSize,
    Nat.mod_eq_of_lt (hs 0)]

/-- `Counter.get` on the stage's scope: it succeeds, returns slot 0 and leaves the storage: the
generic `triple_of_binds` with the binding `get_binds` and no obligation. -/
theorem get_triple {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Triple fuel c (stageScope fnGet []) (fun _ => True) getPost := by
  obtain ⟨d, -, hd, -⟩ := inc_erased hc
  have h := getShape_eq
  simp only [getShape?, hc, Option.some.injEq, Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨-, f, hf, hlen, hT⟩ := h
  exact triple_of_binds hd (by decide) hf hlen hT (fun _ h => by simp at h) get_binds

/-- info: 'SolidCore.Verify.VC.Counter.get_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms get_triple

end SolidCore.Verify.VC.Counter
