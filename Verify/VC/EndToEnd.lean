import Verify.VC.Obligations
import Verify.VC.Discharge
import SolidCore.Refinement.Compose

/-!
# From solar-verify's script to the bytecode, in one theorem

\`bytecode_of_discharged\` composes, for one function the generic source stage erases:

1. the kernel's discharge of solar-verify's whole script (\`dischargeScript cs = true\`, decided by
   \`decide +kernel\`; \`dischargeScript_sound\` gives \`Valid cs\` with no solver verdict);
2. the kernel's check that the script's obligations are the Lean obligations \`obs\`
   (\`checkScript cs obs = true\`);
3. the binding of the function's erased tree to \`obs\` (\`Binds\`), which gives SolidCore's triple
   (\`triple_of_checked\`);
4. a stage from SolidCore's checked contract to the bytecode on the function's scope
   (\`SolarTV.Stage\`, as the certify driver's stages and assembly compose it);

into the run of the exact bytecode under EthLib: every call of the scope runs to an observable
meeting the function's postcondition. Its hypotheses are exactly those four facts (and the deployment
shape \`DeployedAt\`), each a theorem a contract's certificate proves; none is a verdict.
-/

namespace SolidCore.Verify.VC

open SolidCore.Verify SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic
open SolidCore.Solidity

/-- A total-correctness triple of SolidCore's contract carries to the bytecode through a stage. -/
theorem bytecode_of_triple {fuel : Nat} {c : TypeCheck.CheckedContract} {code : ByteArray}
    {scope : Call → Prop} {post : Call → Observable → Prop}
    (stage : SolarTV.Stage (solidCore fuel) ethLib c code scope)
    (ht : Triple fuel c scope (fun _ => True) post) :
    ∀ call, scope call → ∃ obs, Target.run code call = some obs ∧ post call obs := by
  intro call hs
  obtain ⟨hsome, hpost⟩ := ht call hs trivial
  obtain ⟨obs, hobs⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨obs, stage call hs obs hobs, hpost obs hobs⟩

/-- **solar-verify's script, discharged by the kernel, holds of the bytecode.** -/
theorem bytecode_of_discharged {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) {cs : List Cmd} {obs : List (List Tm × Tm)}
    {env : List Nat → Storage → Env} {P : List Nat → Storage → Observable → Prop}
    (hdis : dischargeScript cs = true) (hcheck : checkScript cs obs = true)
    (hbind : Binds fn T obs env P) {code : ByteArray}
    (stage : SolarTV.Stage (solidCore fuel) ethLib c code (stageScope fn s)) :
    ∀ call, stageScope fn s call → ∃ o, Target.run code call = some o ∧ treePost fn P call o :=
  bytecode_of_triple stage
    (triple_of_checked hd hsel hfind hlen hT hcheck (dischargeScript_sound cs hdis) hbind)

/-- **solar-verify's verdict on a script, its obligations checked, holds of the bytecode.** The
verdict may be any proof of `Valid cs`, such as a generated `Discharged.script_valid`. -/
theorem bytecode_of_checked {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) {cs : List Cmd} {obs : List (List Tm × Tm)}
    {env : List Nat → Storage → Env} {P : List Nat → Storage → Observable → Prop}
    (hv : Valid cs) (hcheck : checkScript cs obs = true)
    (hbind : Binds fn T obs env P) {code : ByteArray}
    (stage : SolarTV.Stage (solidCore fuel) ethLib c code (stageScope fn s)) :
    ∀ call, stageScope fn s call → ∃ o, Target.run code call = some o ∧ treePost fn P call o :=
  bytecode_of_triple stage (triple_of_checked hd hsel hfind hlen hT hcheck hv hbind)

end SolidCore.Verify.VC

