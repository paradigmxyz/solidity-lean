import Contracts.Counter.Headline
import SolidCore.Refinement.Deploy

/-!
# Counter's exports, by name, and its deployment

The names the blueprint's statements use for Counter's existing exports: \`code\` (solar's runtime
bytecode), \`spec\` (solar-verify's exported spec) and \`scope\` (\`scopeEvery\`), with \`spec_holds\` the
headline's spec clause about them, and \`deploys\`: solar's init code deploys \`code\` with the empty
storage (\`Deploys\`, from \`Deploy.initcode_runs\`).
-/

namespace Contracts.Counter

open SolidCore.Refinement

/-- solar's runtime bytecode for Counter. -/
abbrev code : ByteArray := SolidCore.Refinement.Solar.Counter.code

/-- solar-verify's exported spec of Counter. -/
abbrev spec : SolidCore.Spec.Bundle := SolidCore.Refinement.Solar.Counter.Headline.spec

/-- Every call the headline covers. -/
abbrev scope : Call → Prop := SolidCore.Refinement.Solar.Counter.scopeEvery

/-- The headline's spec clause: solar-verify's spec of Counter holds of \`code\` under EthLib on
\`scope\`. -/
theorem spec_holds :
    SolidCore.Spec.Holds ethLib code scope spec SolidCore.Refinement.Solar.Counter.Headline.ctxOf
      SolidCore.Refinement.Solar.Counter.Headline.step :=
  SolidCore.Refinement.Solar.Counter.Headline.spec_holds_of_bytecode.2.2.2.choose_spec.2.2.1

/-- **solar's init code deploys Counter's runtime bytecode**, with the empty storage. -/
theorem deploys : Deploys SolidCore.Refinement.Solar.Counter.Deploy.initcode code [] :=
  deploys_of_run SolidCore.Refinement.Solar.Counter.Deploy.initcode_runs rfl rfl (fun _ => rfl)

/-- info: 'Contracts.Counter.deploys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deploys

end Contracts.Counter
