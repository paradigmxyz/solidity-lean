import SolidCoreYulCore.FullYul
import SolidCoreYulCore.SolidityLayout
import SolidCore.Spine.L04_Layout.Interface

namespace SolidCore
namespace Spine
namespace L05_StructuredTarget

abbrev Name := SolidCoreYulCore.FullYul.Name
abbrev Expr := SolidCoreYulCore.FullYul.Expr
abbrev Stmt := SolidCoreYulCore.FullYul.Stmt
abbrev Env := SolidCoreYulCore.FullYul.Env
abbrev FunctionEnv := SolidCoreYulCore.FullYul.FunctionEnv
abbrev Profile := SolidCoreYulCore.FullYul.CompilerProfile

def currentProfile : Profile :=
  SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore

def evalProgramStmtFuel :=
  SolidCoreYulCore.FullYul.evalProgramStmtFuel

end L05_StructuredTarget
end Spine
end SolidCore
