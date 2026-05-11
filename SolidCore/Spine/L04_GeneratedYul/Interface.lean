import SolidCoreYulCore.ConcreteYul
import SolidCore.Spine.L03_AbstractYul.Interface

namespace SolidCore
namespace Spine
namespace L04_GeneratedYul

abbrev Config := SolidCoreYulCore.ConcreteYul.Config
abbrev Result := SolidCoreYulCore.ConcreteYul.Result
abbrev Stmt := SolidCoreYulCore.ConcreteYul.Stmt
abbrev Program := SolidCoreYulCore.ConcreteYul.Program

structure WF (_stmt : Stmt) : Prop where
  generatedFromLayoutSubset : True := by trivial
  noUnsupportedYulSurface : True := by trivial

def evalStmtFuel :=
  SolidCoreYulCore.ConcreteYul.evalStmtFuel

def evalProgramStmtFuel :=
  SolidCoreYulCore.ConcreteYul.evalProgramStmtFuel

end L04_GeneratedYul
end Spine
end SolidCore
