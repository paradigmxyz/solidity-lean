import SolidCore.Solidity.ControlCore
import SolidCore.Spine.L01_ValidSolidity.Interface

namespace SolidCore
namespace Spine
namespace L02_AbstractYul

abbrev Stmt := Solidity.ControlCore.Stmt
abbrev Result := Solidity.ControlCore.Result

def compile := Solidity.ControlCore.Stmt.compile
def compile? := Solidity.ControlCore.Stmt.compile?
def eval := Solidity.ControlCore.Stmt.eval

theorem compile?_sound
    {stmt : L00_SourceSolidity.Stmt} {core : Stmt}
    (hCompile : compile? stmt = some core)
    (fuel : Nat) (context : L00_SourceSolidity.Context)
    (runtime : L00_SourceSolidity.Runtime) :
    eval fuel context runtime core =
      L00_SourceSolidity.evalStmt fuel context runtime stmt :=
  Solidity.ControlCore.Stmt.compile?_sound hCompile fuel context runtime

end L02_AbstractYul
end Spine
end SolidCore
