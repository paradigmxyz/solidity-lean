import SolidCore.Spine.Passes.P01_SourceToCheckedSolidity.Interface
import SolidCore.Spine.Passes.P02_CheckedSolidityToControl.Interface
import SolidCore.Spine.Passes.P03_ControlToEffect.Interface
import SolidCore.Spine.Passes.P04_EffectToLayout.Interface
import SolidCore.Spine.Passes.P05_LayoutToGeneratedYul.Interface
import SolidCore.Spine.Passes.P06_GeneratedYulToStackCfg.Interface
import SolidCore.Spine.Passes.P07_StackCfgToBytecode.Interface
import SolidCore.Spine.Passes.P08_BytecodeToEvm.Interface

namespace SolidCore
namespace Spine
namespace PublicClaims

theorem source_to_control_sound
    {fragment : L01_CheckedSolidity.Fragment}
    {source : L00_Source.Stmt}
    {checked : L01_CheckedSolidity.Program fragment}
    {core : L02_Control.Stmt}
    (hCheck :
      Passes.P01_SourceToCheckedSolidity.check fragment source = some checked)
    (hCompile :
      Passes.P02_CheckedSolidityToControl.compile checked = some core)
    (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) :
    L02_Control.eval fuel context runtime core =
      L00_Source.evalStmt fuel context runtime source := by
  rcases Passes.P01_SourceToCheckedSolidity.check_sound hCheck with
    ⟨hStmt, _hChecked⟩
  simpa [hStmt] using
    Passes.P02_CheckedSolidityToControl.compile_sound
      hCompile fuel context runtime

end PublicClaims
end Spine
end SolidCore
