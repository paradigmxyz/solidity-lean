import SolidCore.Spine.L02_Control.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P02_CheckedSolidityToControl

def compile {fragment : L01_CheckedSolidity.Fragment}
    (program : L01_CheckedSolidity.Program fragment) :
    Option L02_Control.Stmt :=
  L02_Control.compile? program.stmt

theorem compile_sound
    {fragment : L01_CheckedSolidity.Fragment}
    {program : L01_CheckedSolidity.Program fragment}
    {core : L02_Control.Stmt}
    (hCompile : compile program = some core)
    (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) :
    L02_Control.eval fuel context runtime core =
      L00_Source.evalStmt fuel context runtime program.stmt :=
  L02_Control.compile?_sound hCompile fuel context runtime

theorem compile_complete
    {fragment : L01_CheckedSolidity.Fragment}
    (program : L01_CheckedSolidity.Program fragment) :
    ∃ core, compile program = some core := by
  exact
    ⟨L02_Control.compile program.stmt,
      SolidCore.Solidity.ControlCore.Stmt.compile?_complete program.stmt⟩

end P02_CheckedSolidityToControl
end Passes
end Spine
end SolidCore
