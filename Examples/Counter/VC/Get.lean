import Examples.Counter.VC.Inc

/-!
# The certified counter milestone's `get`

`get` carries no NatSpec clause, so solar-verify emits no obligation for it and there is nothing of
solar-verify's to bind: `get_triple` is a direct proof against SolidCore, with the shape of
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

/-- `Counter.get` on the stage's scope: it succeeds, returns slot 0 and leaves the storage, through
`implementsTree`. -/
theorem get_triple {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Triple fuel c (stageScope fnGet []) (fun _ => True) getPost := by
  have hshape := getShape_eq
  simp only [getShape?, hc, Option.some.injEq, Prod.mk.injEq] at hshape
  obtain ⟨hdep, hmap⟩ := hshape
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hmap
  obtain ⟨f, hf, hlen, hT⟩ := hmap
  have himpl := implements_tree (fn := fnGet) hdd (by decide) hf hlen hT rfl
  apply triple_of_wp himpl
  rintro _ ⟨σ, -, fn', hfn', args, hl, hargs, rfl⟩ -
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  obtain rfl : args = [] := List.eq_nil_of_length_eq_zero hl
  have hw : argWords 0 ({ calldata := Abi.calldata fnGet.sel [], callvalue := 0, storage := σ } : Call) =
      [] := argWords_calldata _ [] hargs 0 σ
  rw [vc_eq, treeModel_run, show fnGet.params.length = 0 from rfl, hw]
  set s := initStorage ({ calldata := Abi.calldata fnGet.sel [], callvalue := 0, storage := σ } : Call)
    with hs_def
  have hs : ∀ k, s k < 2 ^ 256 := fun k => Generic.slotValue_lt σ k
  simp only [getPost, ← hs_def]
  refine ⟨rfl, ?_, fun k => rfl⟩
  simp only [getTree, Tree.eval, resOutcome, observe, ite_true, wordOBytes, wordBytes, List.map_map]
  congr 1
  funext i
  have h0 := hs 0
  simp only [Function.comp_apply, OByte.eval, WExpr.eval, valOf, Generic.wordSize, Nat.mod_eq_of_lt h0]

/-- info: 'SolidCore.Verify.VC.Counter.get_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms get_triple

end SolidCore.Verify.VC.Counter
