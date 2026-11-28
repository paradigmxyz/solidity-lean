import Verify.Generic.Expected

/-!
# The evidence a certified contract supplies

`Certificate src spec bytes` is what a contract's proof module provides, and
`Certificate.expected` the one theorem that turns any certificate into `Expected src spec bytes`.
The source translation and the user specification's proof are separate fields, each proved on its
own and composed only here, where the types force them to speak of the same checked contract
(`src.checked`), the same context, the same source semantics and the same valid calls:

* `code`, `bound`: the code the proofs speak of (the fresh export) and the kernel's check that its
  bytes are `bytes`, those the driver's solar compiled in this run;
* `checked`: the type check of solc's AST succeeds (`contract_ok`);
* `translation`: `TranslationAt` in every covered context: what `Shapes.compiled_of` (generic
  source stage, solar-tv's backend stages, the loop checker) and `compiled0XL` (the checker with
  contexts and gas) give, through `translation_of_compiled` (Verify/Generic/Compose.lean), on a
  scope covering the valid calls (`TranslationAt.restrict`: the scope check), with no
  specification;
* `specProof`: the allowed statuses and the postcondition of every source result, proved of the
  same source semantics with no bytes: from solar-verify's export (`specProof_of_holds`), from
  kernel-discharged verification conditions (Verify/Generic/VC.lean), or a reviewed Lean proof;
* `covered`: the coverage checks of `Spec.Covered`.

Loops are in no special position: their termination within the fuel and the stage through them
are part of `translation` (a supplied, kernel-checked ranking certificate and invariant prove
them), and the statement does not change.
-/

namespace SolidCore.Verify.Generic

open SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Solidity

/-- **The evidence of a certified contract.** -/
structure Certificate (src : Source) (spec : Spec) (bytes : List Nat) where
  code : ByteArray
  bound : code.data.toList.map (·.toNat) = bytes
  checked : ∃ c, src.checked = .ok c
  translation : spec.Assumed → ∀ ctx, spec.Contexts ctx → ∀ c, src.checked = .ok c →
    TranslationAt (src.semAt ctx) c ctx code (spec.Valid ctx) (spec.gas ctx)
  specProof : spec.Assumed → ∀ ctx, spec.Contexts ctx → ∀ c, src.checked = .ok c →
    SpecProof (src.semAt ctx) c (spec.Valid ctx) (spec.Allowed ctx) (spec.Post ctx)
  covered : spec.Covered

/-- **Every certificate gives the expected theorem.** -/
theorem Certificate.expected {src : Source} {spec : Spec} {bytes : List Nat}
    (cert : Certificate src spec bytes) : Expected src spec bytes := by
  refine ⟨all_lt_of_eq cert.bound, cert.covered, fun ha ctx hctx => ?_⟩
  obtain ⟨c, hc⟩ := cert.checked
  refine ⟨c, hc, ?_⟩
  rw [runtimeCode_eq cert.bound]
  exact ⟨cert.translation ha ctx hctx c hc, cert.specProof ha ctx hctx c hc⟩

/-! ## Assembling the pieces -/

/-- **The scope check**: a translation proved on a scope covering the valid calls is one on the
valid calls, when some valid call exists. -/
theorem TranslationAt.restrict {S : Sem} {p : S.Prog} {ctx : Context} {code : ByteArray}
    {Scope Valid : Call → Prop} {G : Call → Nat} (h : TranslationAt S p ctx code Scope G)
    (hsub : ∀ call, Valid call → Scope call) (hin : ∃ call, Valid call) :
    TranslationAt S p ctx code Valid G where
  inhabited := hin
  equiv := fun gas hg call hc => h.equiv gas hg call (hsub call hc)
  terminates := fun call hc => h.terminates call (hsub call hc)
  resources := fun call hc => h.resources call (hsub call hc)

/-- The translation with a gas bound given pointwise equal. -/
theorem TranslationAt.congr_gas {S : Sem} {p : S.Prog} {ctx : Context} {code : ByteArray}
    {Valid : Call → Prop} {G G' : Call → Nat} (h : TranslationAt S p ctx code Valid G)
    (he : ∀ call, G call = G' call) : TranslationAt S p ctx code Valid G' := by
  rw [show G' = G from funext fun call => (he call).symm]; exact h

/-- The spec's proof on fewer valid calls. -/
theorem SpecProof.restrict {S : Sem} {p : S.Prog} {Scope Valid : Call → Prop}
    {Allowed Post : Call → Observable → Prop} (h : SpecProof S p Scope Allowed Post)
    (hsub : ∀ call, Valid call → Scope call) : SpecProof S p Valid Allowed Post :=
  ⟨fun call hc => h.allowed call (hsub call hc), fun call hc => h.meets call (hsub call hc)⟩

/-- info: 'SolidCore.Verify.Generic.Certificate.expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Certificate.expected

end SolidCore.Verify.Generic
