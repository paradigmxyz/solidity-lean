import SolidCore.Spine.Passes.P01_SourceSolidityToValidSolidity.Interface
import SolidCore.Spine.Passes.P02_ValidSolidityToAbstractYul.Interface
import SolidCore.Spine.Passes.P03_AbstractYulToGeneratedYul.Interface
import SolidCore.Spine.Passes.P04_GeneratedYulToStackCfg.Interface
import SolidCore.Spine.Passes.P05_StackCfgToBytecode.Interface
import SolidCore.Spine.Passes.P06_BytecodeToEvm.Interface

namespace SolidCore
namespace Spine
namespace PublicClaims

theorem source_to_abstractYul_sound
    {fragment : L01_ValidSolidity.Fragment}
    {source : L00_SourceSolidity.Stmt}
    {valid : L01_ValidSolidity.Program fragment}
    {core : L02_AbstractYul.Stmt}
    (hCheck :
      Passes.P01_SourceSolidityToValidSolidity.check fragment source = some valid)
    (hCompile :
      Passes.P02_ValidSolidityToAbstractYul.compile valid = some core)
    (fuel : Nat) (context : L00_SourceSolidity.Context)
    (runtime : L00_SourceSolidity.Runtime) :
    L02_AbstractYul.eval fuel context runtime core =
      L00_SourceSolidity.evalStmt fuel context runtime source := by
  rcases Passes.P01_SourceSolidityToValidSolidity.check_sound hCheck with
    ⟨hStmt, _hValid⟩
  rw [Passes.P02_ValidSolidityToAbstractYul.compile_sound
      hCompile fuel context runtime]
  exact congrArg
    (fun stmt => L00_SourceSolidity.evalStmt fuel context runtime stmt)
    hStmt

end PublicClaims
end Spine
end SolidCore
