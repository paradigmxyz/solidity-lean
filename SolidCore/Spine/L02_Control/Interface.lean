import SolidCore.Solidity.ControlCore
import SolidCore.Spine.L01_CheckedSolidity.Interface

namespace SolidCore
namespace Spine
namespace L02_Control

abbrev Stmt := Solidity.ControlCore.Stmt
abbrev Result := Solidity.ControlCore.Result

def compile := Solidity.ControlCore.Stmt.compile
def compile? := Solidity.ControlCore.Stmt.compile?
def eval := Solidity.ControlCore.Stmt.eval

theorem compile?_sound
    {stmt : L00_Source.Stmt} {core : Stmt}
    (hCompile : compile? stmt = some core)
    (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) :
    eval fuel context runtime core =
      L00_Source.evalStmt fuel context runtime stmt :=
  Solidity.ControlCore.Stmt.compile?_sound hCompile fuel context runtime

end L02_Control
end Spine
end SolidCore
