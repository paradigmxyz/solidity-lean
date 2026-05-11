import SolidCore.Spine.L02_Control.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P02_AcceptedToControl

def compile := L02_Control.compile?

theorem compile_sound
    {stmt : L00_Source.Stmt} {core : L02_Control.Stmt}
    (hCompile : compile stmt = some core)
    (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) :
    L02_Control.eval fuel context runtime core =
      L00_Source.evalStmt fuel context runtime stmt :=
  L02_Control.compile?_sound hCompile fuel context runtime

theorem compile_complete
    (stmt : L00_Source.Stmt) :
    ∃ core, compile stmt = some core := by
  exact
    ⟨L02_Control.compile stmt,
      SolidCore.Solidity.ControlCore.Stmt.compile?_complete stmt⟩

end P02_AcceptedToControl
end Passes
end Spine
end SolidCore
