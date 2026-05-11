import SolidCore.Spine.L01_Accepted.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P01_SourceToAccepted

def check (fragment : L01_Accepted.Fragment)
    (stmt : L00_Source.Stmt) : Option L00_Source.Stmt :=
  if L01_Accepted.acceptedStmt? fragment stmt then some stmt else none

theorem check_sound
    {fragment : L01_Accepted.Fragment} {stmt checked : L00_Source.Stmt}
    (hCheck : check fragment stmt = some checked) :
    checked = stmt ∧ L01_Accepted.AcceptedSource fragment checked := by
  unfold check at hCheck
  by_cases hAccepted : L01_Accepted.acceptedStmt? fragment stmt
  · simp [hAccepted] at hCheck
    cases hCheck
    exact ⟨rfl, ⟨hAccepted⟩⟩
  · simp [hAccepted] at hCheck

theorem check_complete
    {fragment : L01_Accepted.Fragment} {stmt : L00_Source.Stmt}
    (hAccepted : L01_Accepted.AcceptedSource fragment stmt) :
    check fragment stmt = some stmt := by
  unfold check
  simp [hAccepted.accepted]

end P01_SourceToAccepted
end Passes
end Spine
end SolidCore
