import SolidCoreYulCore.ConcreteYul
import SolidCoreYulCore.Relations
import SolidCore.Spine.L06_SymbolicTarget.Interface

namespace SolidCore
namespace Spine
namespace L07_ConcreteTarget

abbrev Config := SolidCoreYulCore.ConcreteYul.Config
abbrev Result := SolidCoreYulCore.ConcreteYul.Result
abbrev Stmt := SolidCoreYulCore.ConcreteYul.Stmt
abbrev Program := SolidCoreYulCore.ConcreteYul.Program

def evalStmtFuel :=
  SolidCoreYulCore.ConcreteYul.evalStmtFuel

def evalProgramStmtFuel :=
  SolidCoreYulCore.ConcreteYul.evalProgramStmtFuel

end L07_ConcreteTarget
end Spine
end SolidCore
