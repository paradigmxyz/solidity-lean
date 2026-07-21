import SolidCore

set_option maxHeartbeats 8000000

/-!
ITEM-2 byte-identity tripwire: dump the reprStr of the lowered CORE of a
diverse battery of witness contracts. Run before and after the dispatcher
refactor; the outputs must be IDENTICAL strings (hashes compared out of
band). Not part of the build — probes/ only.
-/

namespace CoreDumpBattery

open SolidCore.Solidity
open SolidCore.Solidity.TypeCheck

private def dump (label : String) (decl : ContractDecl) : String :=
  match CheckedInput.ownContract? decl with
  | some checked => label ++ ":" ++ reprStr checked.core.functions
  | none => label ++ ":REJECTED"

private def dumpHash (label : String) (decl : ContractDecl) : String :=
  let s := dump label decl
  label ++ " len=" ++ toString s.length ++ " h=" ++
    toString (s.foldl (fun (a : UInt64) c => a * 31 + c.toNat.toUInt64) 7)

#eval dumpHash "abiEncodeCallArg"
  SolidCore.Solidity.SolcAstImport.AbiEncodeCallArg.importedContract
#eval dumpHash "addressNestedConv"
  SolidCore.Solidity.SolcAstImport.AddressNestedConv.importedContract
#eval dumpHash "boolCastOfComparison"
  SolidCore.Solidity.SolcAstImport.BoolCastOfComparison.importedContract
#eval dumpHash "callPositionConsolidated"
  SolidCore.Solidity.SolcAstImport.CallPositionConsolidated.importedContract
#eval dumpHash "deleteMemoryNestedRef"
  SolidCore.Solidity.SolcAstImport.DeleteMemoryNestedRef.importedContract
#eval dumpHash "enumMemberEncodePacked"
  SolidCore.Solidity.SolcAstImport.EnumMemberEncodePacked.importedContract
#eval dumpHash "expNarrowBaseWideExp"
  SolidCore.Solidity.SolcAstImport.ExpNarrowBaseWideExpWitness.importedContract
#eval dumpHash "envLoweringUnify"
  SolidCore.Solidity.SolcAstImport.EnvLoweringUnifyWitness.importedContract
#eval dumpHash "evalOrderIntrinsic"
  SolidCore.Solidity.SolcAstImport.EvalOrderIntrinsic.importedContract
#eval dumpHash "loweringUnify"
  SolidCore.Solidity.SolcAstImport.LoweringUnifyWitness.importedContract
#eval dumpHash "libStorageReturn"
  SolidCore.Solidity.SolcAstImport.LibStorageReturn.importedContract
#eval dumpHash "anfCallHoisting"
  SolidCore.Solidity.SolcAstImport.AnfCallHoisting.importedContract
#eval dumpHash "emitStorageDynamicArray"
  SolidCore.Solidity.SolcAstImport.EmitStorageDynamicArray.importedContract
#eval dumpHash "abiDecodeStorageBytes"
  SolidCore.Solidity.SolcAstImport.AbiDecodeStorageBytes.importedContract
#eval dumpHash "svunNestedTuple"
  SolidCore.Solidity.SolcAstImport.StorageValueUseNormalize.nestedTupleContract
#eval dumpHash "svunStructCtor"
  SolidCore.Solidity.SolcAstImport.StorageValueUseNormalize.structCtorContract
#eval dumpHash "svunConcat"
  SolidCore.Solidity.SolcAstImport.StorageValueUseNormalize.concatContract
#eval dumpHash "svunRequireCustom"
  SolidCore.Solidity.SolcAstImport.StorageValueUseNormalize.requireCustomContract
#eval dumpHash "svunRevertReason"
  SolidCore.Solidity.SolcAstImport.StorageValueUseNormalize.revertReasonContract
#eval dumpHash "svunArrayLiteralSource"
  SolidCore.Solidity.SolcAstImport.StorageValueUseNormalize.arrayLiteralSourceContract
#eval dumpHash "svunPointerArrayLiteralSource"
  SolidCore.Solidity.SolcAstImport.StorageValueUseNormalize.pointerArrayLiteralSourceContract

end CoreDumpBattery
