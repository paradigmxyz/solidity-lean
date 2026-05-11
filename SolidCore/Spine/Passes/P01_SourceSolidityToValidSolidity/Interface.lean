import SolidCore.Spine.L01_ValidSolidity.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P01_SourceSolidityToValidSolidity

def check (fragment : L01_ValidSolidity.Fragment)
    (stmt : L00_SourceSolidity.Stmt) :
    Option (L01_ValidSolidity.Program fragment) :=
  if hFragment : L01_ValidSolidity.inFragmentStmt? fragment stmt = true then
    some { stmt := stmt, valid := { inFragment := hFragment } }
  else
    none

theorem check_sound
    {fragment : L01_ValidSolidity.Fragment} {stmt : L00_SourceSolidity.Stmt}
    {program : L01_ValidSolidity.Program fragment}
    (hCheck : check fragment stmt = some program) :
    program.stmt = stmt ∧
      L01_ValidSolidity.ValidSource fragment program.stmt := by
  unfold check at hCheck
  by_cases hFragment :
      L01_ValidSolidity.inFragmentStmt? fragment stmt = true
  · simp [hFragment] at hCheck
    cases hCheck
    exact ⟨rfl, { inFragment := hFragment }⟩
  · simp [hFragment] at hCheck

theorem check_complete
    {fragment : L01_ValidSolidity.Fragment} {stmt : L00_SourceSolidity.Stmt}
    (hValid : L01_ValidSolidity.ValidSource fragment stmt) :
    ∃ program : L01_ValidSolidity.Program fragment,
      check fragment stmt = some program ∧ program.stmt = stmt := by
  refine ⟨{ stmt := stmt, valid := hValid }, ?_, rfl⟩
  unfold check
  simp [hValid.inFragment]

end P01_SourceSolidityToValidSolidity
end Passes
end Spine
end SolidCore
