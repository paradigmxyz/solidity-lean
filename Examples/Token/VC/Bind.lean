import Examples.Token.VC.Export

/-!
# The exported scripts are solar-verify's transcripts

Each exported `script` prints back to its `transcript`, the bytes solar-verify wrote with
`--dump-smt` in the same run. The check runs Lean's evaluator: the kernel's evaluation of the
printer on a transcript of 20 KB, with its 78-digit numerals, does not fit in this build's memory.
-/

namespace SolidCore.Verify.VC

#guard printScript Export.{c}.script == Export.{c}.transcript

end SolidCore.Verify.VC
