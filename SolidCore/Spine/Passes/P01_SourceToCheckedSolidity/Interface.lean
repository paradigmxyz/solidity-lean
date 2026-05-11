import SolidCore.Spine.L01_CheckedSolidity.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P01_SourceToCheckedSolidity

def check (fragment : L01_CheckedSolidity.Fragment)
    (stmt : L00_Source.Stmt) :
    Option (L01_CheckedSolidity.Program fragment) :=
  if hFragment : L01_CheckedSolidity.inFragmentStmt? fragment stmt = true then
    some { stmt := stmt, checked := { inFragment := hFragment } }
  else
    none

theorem check_sound
    {fragment : L01_CheckedSolidity.Fragment} {stmt : L00_Source.Stmt}
    {program : L01_CheckedSolidity.Program fragment}
    (hCheck : check fragment stmt = some program) :
    program.stmt = stmt ∧
      L01_CheckedSolidity.CheckedSource fragment program.stmt := by
  unfold check at hCheck
  by_cases hFragment :
      L01_CheckedSolidity.inFragmentStmt? fragment stmt = true
  · simp [hFragment] at hCheck
    cases hCheck
    exact ⟨rfl, { inFragment := hFragment }⟩
  · simp [hFragment] at hCheck

theorem check_complete
    {fragment : L01_CheckedSolidity.Fragment} {stmt : L00_Source.Stmt}
    (hChecked : L01_CheckedSolidity.CheckedSource fragment stmt) :
    ∃ program : L01_CheckedSolidity.Program fragment,
      check fragment stmt = some program ∧ program.stmt = stmt := by
  refine ⟨{ stmt := stmt, checked := hChecked }, ?_, rfl⟩
  unfold check
  simp [hChecked.inFragment]

end P01_SourceToCheckedSolidity
end Passes
end Spine
end SolidCore
