import SolidCore.Spine.L03_AbstractYul.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P03_DesugaredSolidityToAbstractYul

def compile {fragment : L01_CheckedSolidity.Fragment}
    (program : L02_DesugaredSolidity.Program fragment) :
    Option L03_AbstractYul.Stmt :=
  L03_AbstractYul.compile? program.stmt

theorem compile_sound
    {fragment : L01_CheckedSolidity.Fragment}
    {program : L02_DesugaredSolidity.Program fragment}
    {core : L03_AbstractYul.Stmt}
    (hCompile : compile program = some core)
    (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) :
    L03_AbstractYul.eval fuel context runtime core =
      L00_Source.evalStmt fuel context runtime program.stmt :=
  L03_AbstractYul.compile?_sound hCompile fuel context runtime

theorem compile_complete
    {fragment : L01_CheckedSolidity.Fragment}
    (program : L02_DesugaredSolidity.Program fragment) :
    ∃ core, compile program = some core := by
  exact
    ⟨L03_AbstractYul.compile program.stmt,
      SolidCore.Solidity.ControlCore.Stmt.compile?_complete program.stmt⟩

end P03_DesugaredSolidityToAbstractYul
end Passes
end Spine
end SolidCore
