import SolidCore.Spine.L05_StructuredTarget.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P05_LayoutToStructuredTarget

structure Artifact where
  stmt : L05_StructuredTarget.Stmt
  fuel : Nat
  profile : L05_StructuredTarget.Profile := L05_StructuredTarget.currentProfile

def compile? (_stmt : L04_Layout.Stmt) : Option Artifact :=
  none

structure SoundnessBoundary (_stmt : L04_Layout.Stmt)
    (_artifact : Artifact) : Prop where
  sourceToTargetRelationNamed : True := by trivial

end P05_LayoutToStructuredTarget
end Passes
end Spine
end SolidCore
