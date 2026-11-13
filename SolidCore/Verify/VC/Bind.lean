import SolidCore.Verify.VC.Export.Counter
import SolidCore.Verify.VC.Export.Token

/-!
# The exported scripts are solar-verify's transcripts

Each exported `script` prints back to its `transcript`, the bytes solar-verify wrote with
`--dump-smt` in the same run. The check runs Lean's evaluator: the kernel's evaluation of the
printer on a transcript of 20 KB, with its 78-digit numerals, does not fit in this build's memory.
-/

namespace SolidCore.Verify.VC

#guard printScript Export.Counter.script == Export.Counter.transcript
#guard printScript Export.Token.script == Export.Token.transcript

end SolidCore.Verify.VC
