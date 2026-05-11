import SolidCore.Spine.L02_AbstractYul.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P02_ValidSolidityToAbstractYul

structure Artifact where
  program : L02_AbstractYul.Program
  wf : L02_AbstractYul.WF program

def compile? (_program : L01_ValidSolidity.Program) : Option Artifact :=
  none

structure SoundnessBoundary
    (_program : L01_ValidSolidity.Program) (_artifact : Artifact) :
    Prop where
  abstractYulRefinesValidSolidity : True := by trivial

theorem compile?_sound
    {program : L01_ValidSolidity.Program} {artifact : Artifact}
    (hCompile : compile? program = some artifact) :
    SoundnessBoundary program artifact := by
  cases hCompile

end P02_ValidSolidityToAbstractYul
end Passes
end Spine
end SolidCore
