import SolidCore.Spine.L02_DesugaredSolidity.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P02_CheckedSolidityToDesugaredSolidity

def compile {fragment : L01_CheckedSolidity.Fragment}
    (program : L01_CheckedSolidity.Program fragment) :
    L02_DesugaredSolidity.Program fragment :=
  L02_DesugaredSolidity.fromChecked program

theorem compile_sound {fragment : L01_CheckedSolidity.Fragment}
    (program : L01_CheckedSolidity.Program fragment)
    (fuel : Nat) (context : L00_Source.Context)
    (runtime : L00_Source.Runtime) :
    L02_DesugaredSolidity.eval fuel context runtime (compile program).stmt =
      L00_Source.evalStmt fuel context runtime program.stmt :=
  L02_DesugaredSolidity.fromChecked_eval program fuel context runtime

end P02_CheckedSolidityToDesugaredSolidity
end Passes
end Spine
end SolidCore
