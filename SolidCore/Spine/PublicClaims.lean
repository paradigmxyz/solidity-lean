import SolidCore.Spine.Passes.P01_SourceToCheckedSolidity.Interface
import SolidCore.Spine.Passes.P02_CheckedSolidityToDesugaredSolidity.Interface
import SolidCore.Spine.Passes.P03_DesugaredSolidityToAbstractYul.Interface
import SolidCore.Spine.Passes.P04_AbstractYulToGeneratedYul.Interface
import SolidCore.Spine.Passes.P05_GeneratedYulToStackCfg.Interface
import SolidCore.Spine.Passes.P06_StackCfgToBytecode.Interface
import SolidCore.Spine.Passes.P07_BytecodeToEvm.Interface

namespace SolidCore
namespace Spine
namespace PublicClaims

theorem source_to_abstractYul_sound
    {fragment : L01_CheckedSolidity.Fragment}
    {source : L00_Source.Stmt}
    {checked : L01_CheckedSolidity.Program fragment}
    {desugared : L02_DesugaredSolidity.Program fragment}
    {core : L03_AbstractYul.Stmt}
    (hCheck :
      Passes.P01_SourceToCheckedSolidity.check fragment source = some checked)
    (hDesugar :
      Passes.P02_CheckedSolidityToDesugaredSolidity.compile checked =
        desugared)
    (hCompile :
      Passes.P03_DesugaredSolidityToAbstractYul.compile desugared = some core)
    (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) :
    L03_AbstractYul.eval fuel context runtime core =
      L00_Source.evalStmt fuel context runtime source := by
  rcases Passes.P01_SourceToCheckedSolidity.check_sound hCheck with
    ⟨hStmt, _hChecked⟩
  have hDesugarSound :=
    Passes.P02_CheckedSolidityToDesugaredSolidity.compile_sound
      checked fuel context runtime
  rw [hDesugar] at hDesugarSound
  have hDesugarSound' :
      L00_Source.evalStmt fuel context runtime desugared.stmt =
      L00_Source.evalStmt fuel context runtime checked.stmt := by
    simpa [L02_DesugaredSolidity.eval] using hDesugarSound
  rw [Passes.P03_DesugaredSolidityToAbstractYul.compile_sound
      hCompile fuel context runtime]
  rw [hDesugarSound']
  exact congrArg
    (fun stmt => L00_Source.evalStmt fuel context runtime stmt)
    hStmt

end PublicClaims
end Spine
end SolidCore
