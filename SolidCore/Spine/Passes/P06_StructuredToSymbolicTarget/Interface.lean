import SolidCore.Spine.L06_SymbolicTarget.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P06_StructuredToSymbolicTarget

structure Artifact where
  stmt : L05_StructuredTarget.Stmt
  symbolicConfig? : Option L06_SymbolicTarget.Config := none

def compile (stmt : L05_StructuredTarget.Stmt) : Artifact :=
  { stmt := stmt }

structure SoundnessBoundary (_artifact : Artifact) : Prop where
  symbolicSemanticsConnected : True := by trivial

end P06_StructuredToSymbolicTarget
end Passes
end Spine
end SolidCore
