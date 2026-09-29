import SolidCore.Solidity.Interpreter

/-!
The allocation bound used by `abi.decode` is relative to the current EVM
free-memory pointer. A length that fits when memory is still at `0x80` can cross
the `2^64 - 1` limit after a preceding 100000-byte allocation.
-/

namespace SolidCore.Solidity.Witness.AbiDecodeCurrentMemoryPtr

open SolidCore.Solidity.Source

private def length : Word := 576460752303420482

def fitsAtInitialPointer : Bool :=
  match abiCheckAllocationAt? 0x80 false length with
  | Except.ok () => true
  | _ => false

def panicsAtAdvancedPointer : Bool :=
  match abiCheckAllocationAt? 100256 false length with
  | Except.error RevertData.memoryAllocationTooLarge => true
  | _ => false

#guard fitsAtInitialPointer
#guard panicsAtAdvancedPointer

end SolidCore.Solidity.Witness.AbiDecodeCurrentMemoryPtr
