import Verify.VC.Discharge
import Verify.Spec.Contract

/-!
# Binding solar-verify's script to a stage's semantics

\`ScriptBinds script S p scope b ctxOf step\`: the kernel's check \`checkScript\` finds, among the
obligations of solar-verify's script \`script\`, Lean obligations \`obs\` whose validity gives the
spec \`b\` of the program \`p\` in the semantics \`S\` on \`scope\` (\`SolidCore.Spec.Holds\`). The
implication is where a contract's binding lives: per function, \`triple_of_binds\`
(Verify/VC/Obligations.lean) turns a function's erased tree and its obligations into SolidCore's
triple, and the stages carry it to the bytecode (\`Holds.of_stage\`).

* \`holds_of_valid_script\`: a binding and solar-verify's verdict \`Valid script\` give the spec.
* \`holds_of_discharged\`: a binding and the kernel's \`dischargeScript script = true\` give the spec
  with no verdict (\`dischargeScript_sound\`, Verify/VC/Discharge.lean).
-/

namespace SolidCore.Verify.VC

open SolidCore.Spec

/-- solar-verify's script \`script\` binds the spec \`b\` of \`p\` in \`S\`: some Lean obligations the
kernel finds in the script give it when they are valid. -/
def ScriptBinds (script : List Cmd) (S : SolarTV.Sem) (p : S.Prog) (scope : SolarTV.Call → Prop)
    (b : Bundle) (ctxOf : SolarTV.Call → Ctx) (step : GhostStep) : Prop :=
  ∃ obs : List (List Tm × Tm), checkScript script obs = true ∧
    (ObsValid obs → Holds S p scope b ctxOf step)

/-- **A bound script's verdict gives the spec.** -/
theorem holds_of_valid_script {S : SolarTV.Sem} {p : S.Prog} {scope : SolarTV.Call → Prop}
    {b : Bundle} {ctxOf : SolarTV.Call → Ctx} {step : GhostStep}
    (script : List Cmd) (bind : ScriptBinds script S p scope b ctxOf step)
    (valid : Valid script) : Holds S p scope b ctxOf step := by
  obtain ⟨obs, hcheck, himp⟩ := bind
  exact himp (checkScript_sound hcheck valid)

/-- **A bound script the kernel discharges gives the spec**, with no solver verdict. -/
theorem holds_of_discharged {S : SolarTV.Sem} {p : S.Prog} {scope : SolarTV.Call → Prop}
    {b : Bundle} {ctxOf : SolarTV.Call → Ctx} {step : GhostStep}
    (script : List Cmd) (bind : ScriptBinds script S p scope b ctxOf step)
    (h : dischargeScript script = true) : Holds S p scope b ctxOf step :=
  holds_of_valid_script script bind (dischargeScript_sound script h)

end SolidCore.Verify.VC
