import SolidCore.Refinement.Dyn.Evm
import SolidCore.Refinement.Dyn.Source

/-!
# The refinement on dynamic parameters and malformed call data

`refines_dyn` joins the two halves of a contract's proof on `Dyn.dynScope`: the
refinement on the canonical encodings `Dyn.encodings` (checked by evaluation, with
`native_decide`) and, for malformed call data, SolidCore's rejection
(`run_malformed`, once `native_decide` checks each function's shape) and EthLib's
(`TargetMalformed`, proved symbolically by `dyn_symex`).

The statement is
```
Refines fuel c code (dynScope fns s)
```
for the deployed storage `s`: every call of every function of `fns` on a canonical
encoding within the bounds, and every call of one of them on its selector followed by
malformed bytes of any length below `2 ^ 32`.
-/

namespace SolidCore.Refinement.Dyn

open SolidCore.Refinement.Abi SolidCore.Solidity

/-- EthLib rejects every call of a function of `fns` on malformed call data shorter than
`2 ^ 32`, from any storage: the per-contract fact `dyn_symex` proves. -/
def TargetMalformed (code : ByteArray) (fns : List DFn) : Prop :=
  ∀ fn ∈ fns, ∀ (σ : List (Nat × Nat)) (data : ByteArray), data.size < 2 ^ 32 →
    Malformed fn.params data → Target.run code (callOn fn.sel data σ) = some (rejected σ)

/-- The refinement on the canonical encodings, the shape of every function and EthLib's
rejection of malformed call data give the refinement on `dynScope`. -/
theorem refines_dyn {fuel : Nat} {c : TypeCheck.CheckedContract} {code : ByteArray}
    {s : List (Nat × Nat)} {fns : List DFn} (hdep : deployedStorage fuel c = some s)
    (henc : Refines fuel c code (· ∈ encodings fns [s]))
    (hshape : fns.all (dfnShapeOk c) = true) (htgt : TargetMalformed code fns) :
    Refines fuel c code (dynScope fns s) := by
  rintro _ (hc | ⟨fn, hfn, data, hsz, hm, rfl⟩)
  · exact henc _ hc
  · exact ⟨_, run_malformed hdep fn (List.all_eq_true.mp hshape fn hfn) s data hm,
      htgt fn hfn s data hsz hm⟩

end SolidCore.Refinement.Dyn
