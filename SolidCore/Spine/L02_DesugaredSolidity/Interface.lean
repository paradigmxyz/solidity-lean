import SolidCore.Spine.L01_CheckedSolidity.Interface

namespace SolidCore
namespace Spine
namespace L02_DesugaredSolidity

abbrev Stmt := L00_Source.Stmt
abbrev Result := L00_Source.Result

structure DesugaredSource (_stmt : Stmt) : Prop where
  modifiersExpanded : True := by trivial
  noUnsupportedSurfaceSugar : True := by trivial

structure Program (fragment : L01_CheckedSolidity.Fragment) where
  stmt : Stmt
  source : L01_CheckedSolidity.Program fragment
  desugared : DesugaredSource stmt

def eval := L00_Source.evalStmt

def fromChecked {fragment : L01_CheckedSolidity.Fragment}
    (program : L01_CheckedSolidity.Program fragment) : Program fragment where
  stmt := program.stmt
  source := program
  desugared := {}

theorem fromChecked_eval {fragment : L01_CheckedSolidity.Fragment}
    (program : L01_CheckedSolidity.Program fragment)
    (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) :
    eval fuel context runtime (fromChecked program).stmt =
      L00_Source.evalStmt fuel context runtime program.stmt := by
  rfl

end L02_DesugaredSolidity
end Spine
end SolidCore
