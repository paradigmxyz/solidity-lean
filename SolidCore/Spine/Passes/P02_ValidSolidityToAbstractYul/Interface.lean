import SolidCore.Spine.L02_AbstractYul.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P02_ValidSolidityToAbstractYul

def compile {fragment : L01_ValidSolidity.Fragment}
    (program : L01_ValidSolidity.Program fragment) :
    Option L02_AbstractYul.Stmt :=
  L02_AbstractYul.compile? program.stmt

theorem compile_sound
    {fragment : L01_ValidSolidity.Fragment}
    {program : L01_ValidSolidity.Program fragment}
    {core : L02_AbstractYul.Stmt}
    (hCompile : compile program = some core)
    (fuel : Nat) (context : L00_SourceSolidity.Context)
    (runtime : L00_SourceSolidity.Runtime) :
    L02_AbstractYul.eval fuel context runtime core =
      L00_SourceSolidity.evalStmt fuel context runtime program.stmt :=
  L02_AbstractYul.compile?_sound hCompile fuel context runtime

theorem compile_complete
    {fragment : L01_ValidSolidity.Fragment}
    (program : L01_ValidSolidity.Program fragment) :
    ∃ core, compile program = some core := by
  exact
    ⟨L02_AbstractYul.compile program.stmt,
      SolidCore.Solidity.ControlCore.Stmt.compile?_complete program.stmt⟩

end P02_ValidSolidityToAbstractYul
end Passes
end Spine
end SolidCore
