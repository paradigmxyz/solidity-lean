import SolidCore.Spine.Passes.P01_SourceToAccepted.Interface
import SolidCore.Spine.Passes.P02_AcceptedToControl.Interface
import SolidCore.Spine.Passes.P03_ControlToEffect.Interface
import SolidCore.Spine.Passes.P04_EffectToLayout.Interface
import SolidCore.Spine.Passes.P05_LayoutToStructuredTarget.Interface
import SolidCore.Spine.Passes.P06_StructuredToSymbolicTarget.Interface
import SolidCore.Spine.Passes.P07_SymbolicToConcreteTarget.Interface
import SolidCore.Spine.Passes.P08_ConcreteToStackCfg.Interface
import SolidCore.Spine.Passes.P09_StackCfgToBytecode.Interface
import SolidCore.Spine.Passes.P10_BytecodeToEvm.Interface

namespace SolidCore
namespace Spine
namespace PublicClaims

theorem source_to_control_sound
    {fragment : L01_Accepted.Fragment}
    {source checked : L00_Source.Stmt}
    {core : L02_Control.Stmt}
    (hCheck :
      Passes.P01_SourceToAccepted.check fragment source = some checked)
    (hCompile :
      Passes.P02_AcceptedToControl.compile checked = some core)
    (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) :
    L02_Control.eval fuel context runtime core =
      L00_Source.evalStmt fuel context runtime source := by
  rcases Passes.P01_SourceToAccepted.check_sound hCheck with
    ⟨hChecked, _hAccepted⟩
  subst checked
  exact
    Passes.P02_AcceptedToControl.compile_sound
      hCompile fuel context runtime

end PublicClaims
end Spine
end SolidCore
