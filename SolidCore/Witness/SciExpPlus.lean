/-
Divergence #159 SCIENTIFIC-EXP-PLUS witness (over-accept, witness-only).

Solidity 0.8.35's number scanner permits an OPTIONAL '-' in a
scientific-notation exponent, but NEVER a leading '+'. Pinned solc rejects
`1e+5`, `1E+5`, `1.0e+2`, `2e+3 seconds` at scan time ("Invalid literal
value"); it accepts `1e5` (no sign) and `1e-5` (minus). Because the rejected
literals never produce an AST, this divergence is witness-only: there is no
importable fixture and no forge lane. We pin the boundary directly on the
number parser `parseNumberRat?`.

The fix dropped the `'+' :: rest` branch in `parseDecimalExponentSuffix?` so a
leading '+' in an exponent parses to `none` (reject). Kept in the built library
so `lake build` regression-guards it.
-/
import SolidCore.Solidity.Interface

namespace SolidCore
namespace Solidity
namespace Executable
namespace SciExpPlus

-- Over-accept fix: a '+' sign in the exponent is now REJECTED (matches solc).
theorem plusExponentRejected : parseNumberRat? "1e+5" = none := rfl
theorem plusExponentUpperRejected : parseNumberRat? "1E+5" = none := rfl
theorem plusExponentFracRejected : parseNumberRat? "1.0e+2" = none := rfl

-- No regression: the accepted forms still parse to their exact rational value.
theorem noSignAccepted :
    parseNumberRat? "1e5" = some { num := 100000, den := 1 } := rfl
theorem minusExponentAccepted :
    parseNumberRat? "1e-5" = some { num := 1, den := 100000 } := rfl
theorem fracMantissaAccepted :
    parseNumberRat? "2.5e10" = some { num := 25000000000, den := 1 } := rfl

-- Boolean mirrors for the manifest eval lane.
def plusExponentRejects : Bool := (parseNumberRat? "1e+5").isNone
def noSignParses : Bool := (parseNumberRat? "1e5").isSome
def minusExponentParses : Bool := (parseNumberRat? "1e-5").isSome

end SciExpPlus
end Executable
end Solidity
end SolidCore
