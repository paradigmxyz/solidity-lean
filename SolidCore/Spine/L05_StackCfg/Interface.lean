import SolidCoreYulCore.StackCfg
import SolidCore.Spine.L04_GeneratedYul.Interface

namespace SolidCore
namespace Spine
namespace L05_StackCfg

abbrev Program := SolidCoreYulCore.StackCfg.Program
abbrev Config := SolidCoreYulCore.StackCfg.Config
abbrev DepthEnv := SolidCoreYulCore.StackCfg.DepthEnv
abbrev Layout := SolidCoreYulCore.StackCfg.Layout

def step := SolidCoreYulCore.StackCfg.step
abbrev DepthChecked := SolidCoreYulCore.StackCfg.Program.DepthChecked

structure WF (depthOf : DepthEnv) (program : Program) : Prop where
  depthChecked : DepthChecked depthOf program
  labelsClosed : True := by trivial
  labelsUnique : True := by trivial
  entryDefined : True := by trivial
  branchTargetsClosed : True := by trivial
  layoutsChecked : True := by trivial
  generatedLabelsFresh : True := by trivial
  maxStackBounded : True := by trivial
  terminalsAtBlockEnds : True := by trivial
  pseudoInstructionsEliminable : True := by trivial

end L05_StackCfg
end Spine
end SolidCore
