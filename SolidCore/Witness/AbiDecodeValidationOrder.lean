import SolidCore.Solidity.Interpreter

/-!
`abi.decode` validates top-level components in source order. A dirty first
`uint8` therefore reverts empty before decoding a later oversized dynamic-array
length that would independently raise Panic(0x41).
-/

namespace SolidCore.Solidity.Witness.AbiDecodeValidationOrder

open SolidCore.Solidity.Source

private def word32 (value : Word) : List Byte :=
  wordToBytesBE 32 value

def dirtyThenOversized : List Byte :=
  word32 0x100 ++ word32 0x40 ++ word32 (2 ^ 255)

def revertsEmpty : Bool :=
  match
      abiDecodeValuesWithCleanupsExcept?
        [Ty.uint256, Ty.dynamicArray Ty.uint256]
        [AbiCleanup.uint 8, AbiCleanup.dynamicArray AbiCleanup.none]
        dirtyThenOversized with
  | Except.error RevertData.empty => true
  | _ => false

def laterAllocationWouldPanic : Bool :=
  match abiDecodeValuesExcept?
      [Ty.uint256, Ty.dynamicArray Ty.uint256] dirtyThenOversized with
  | Except.error RevertData.memoryAllocationTooLarge => true
  | _ => false

#guard revertsEmpty
#guard laterAllocationWouldPanic

end SolidCore.Solidity.Witness.AbiDecodeValidationOrder
