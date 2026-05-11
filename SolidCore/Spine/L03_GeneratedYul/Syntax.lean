import SolidCore.Spine.L02_AbstractYul.Syntax
import SolidCoreYulCore.Evm

namespace SolidCore
namespace Spine
namespace L03_GeneratedYul
namespace Syntax

abbrev Word := SolidCoreYulCore.Word
abbrev Byte := Nat
abbrev Name := Nat
abbrev DataLabel := Nat
abbrev Builtin := SolidCoreYulCore.Evm.Builtin

inductive MemoryRegion where
  | scratch
  | freePointer
  | calldata
  | returndata
  | abiInput
  | abiOutput
  | revertOutput
  deriving Repr

structure StorageSlot where
  base : Word
  keys : List Word := []
  deriving Repr

structure LayoutItem where
  sourceStorage : L01_ValidSolidity.Syntax.StorageId
  slot : StorageSlot
  deriving Repr

structure AbiItem where
  sourceFunction : L01_ValidSolidity.Syntax.FunctionId
  selector : Word
  calldataTypes : List L02_AbstractYul.Syntax.Ty := []
  returndataTypes : List L02_AbstractYul.Syntax.Ty := []
  deriving Repr

structure EventItem where
  sourceEvent : L01_ValidSolidity.Syntax.EventId
  topic0 : Option Word := none
  indexedCount : Nat := 0
  deriving Repr

structure ErrorItem where
  sourceError : L01_ValidSolidity.Syntax.ErrorId
  selector : Word
  deriving Repr

inductive Expr where
  | word : Word -> Expr
  | var : Name -> Expr
  | builtin : Builtin -> List Expr -> Expr
  | call : Name -> List Expr -> Expr
  | dataSize : DataLabel -> Expr
  | dataOffset : DataLabel -> Expr
  deriving Repr

inductive Stmt where
  | skip
  | expr : Expr -> Stmt
  | let1 : Name -> Option Expr -> Stmt
  | letMany : List Name -> Option (List Expr) -> Stmt
  | assign : Name -> Expr -> Stmt
  | assignMany : List Name -> List Expr -> Stmt
  | function : Name -> List Name -> List Name -> Stmt -> Stmt
  | block : List Stmt -> Stmt
  | ifThen : Expr -> Stmt -> Stmt
  | switch : Expr -> List (Word × Stmt) -> Option Stmt -> Stmt
  | forLoop : Stmt -> Expr -> Stmt -> Stmt -> Stmt
  | break
  | continue
  | leave
  deriving Repr

structure FunctionDef where
  name : Name
  params : List Name := []
  returns : List Name := []
  body : Stmt
  deriving Repr

structure DataSegment where
  label : DataLabel
  bytes : List Byte := []
  deriving Repr

structure Object where
  code : Stmt
  functions : List FunctionDef := []
  data : List DataSegment := []
  subobjects : List (DataLabel × Object) := []
  deriving Repr

structure Profile where
  layout : List LayoutItem := []
  abi : List AbiItem := []
  events : List EventItem := []
  errors : List ErrorItem := []
  memoryRegions : List MemoryRegion := []
  emittedHelpers : List Name := []
  deriving Repr

structure Program where
  object : Object
  profile : Profile := {}
  deriving Repr

end Syntax
end L03_GeneratedYul
end Spine
end SolidCore
