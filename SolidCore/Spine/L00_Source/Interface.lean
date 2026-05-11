import SolidCore.Solidity.ABI
import SolidCore.Solidity.ControlCore
import SolidCore.Solidity.Interpreter

namespace SolidCore
namespace Spine
namespace L00_Source

abbrev Expr := Solidity.Source.Expr
abbrev Stmt := Solidity.Source.Stmt
abbrev Context := Solidity.Source.Context
abbrev Runtime := Solidity.Source.Runtime
abbrev Result := Solidity.Source.Result
abbrev State := Solidity.Source.State
abbrev Contract := Solidity.Source.Contract

def evalStmt := Solidity.Source.Stmt.eval
def evalList := Solidity.Source.Stmt.evalList

end L00_Source
end Spine
end SolidCore
