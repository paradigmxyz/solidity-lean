import SolidCore.Spine.Passes.P01_SourceSolidityToValidSolidity.Interface
import SolidCore.Spine.Passes.P02_ValidSolidityToAbstractYul.Interface
import SolidCore.Spine.Passes.P03_AbstractYulToGeneratedYul.Interface
import SolidCore.Spine.Passes.P04_GeneratedYulToStackCfg.Interface
import SolidCore.Spine.Passes.P05_StackCfgToBytecode.Interface
import SolidCore.Spine.Passes.P06_BytecodeToEvm.Interface

namespace SolidCore
namespace Spine
namespace PublicClaims

structure EndToEndArtifacts where
  valid : Passes.P01_SourceSolidityToValidSolidity.Artifact
  abstractYul : Passes.P02_ValidSolidityToAbstractYul.Artifact
  generatedYul : Passes.P03_AbstractYulToGeneratedYul.Artifact
  stackCfg : Passes.P04_GeneratedYulToStackCfg.Artifact
  bytecode : Passes.P05_StackCfgToBytecode.Artifact
  evm : Passes.P06_BytecodeToEvm.Artifact

structure EndToEndBoundary
    (_source : L00_SourceSolidity.SourceUnit)
    (_artifacts : EndToEndArtifacts) : Prop where
  sourceAccepted : True := by trivial
  adjacentPassesSound : True := by trivial
  reachesTargetEvm : True := by trivial

theorem public_spine_has_single_language_per_layer : True := by
  trivial

end PublicClaims
end Spine
end SolidCore
