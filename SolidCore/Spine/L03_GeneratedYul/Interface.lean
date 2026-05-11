import SolidCoreYulCore.ConcreteYul
import SolidCore.Spine.L02_AbstractYul.Interface

namespace SolidCore
namespace Spine
namespace L03_GeneratedYul

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

end L03_GeneratedYul
end Spine
end SolidCore
