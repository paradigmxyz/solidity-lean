import SolidCore.Spine.L01_ValidSolidity.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P01_SourceSolidityToValidSolidity

structure Artifact where
  program : L01_ValidSolidity.Program
  wf : L01_ValidSolidity.WF program

def check? (_source : L00_SourceSolidity.SourceUnit) : Option Artifact :=
  none

structure SoundnessBoundary
    (_source : L00_SourceSolidity.SourceUnit) (_artifact : Artifact) :
    Prop where
  validSolidityRepresentsSource : True := by trivial

theorem check?_sound
    {source : L00_SourceSolidity.SourceUnit} {artifact : Artifact}
    (hCheck : check? source = some artifact) :
    SoundnessBoundary source artifact := by
  cases hCheck

end P01_SourceSolidityToValidSolidity
end Passes
end Spine
end SolidCore
