/-
Surface Solidity AST (Phase 3, sub-step b split out of Interface.lean).

Pure pre-validity AST types (expressions, statements, declarations, source
units). Elaboration to the executable core and the (Phase 4) observation layer
live in Interface.lean, which imports this module.
-/
import SolidCore.Solidity.Shared.Precompile
import SolidCore.Solidity.Shared.Word

namespace SolidCore
namespace Solidity

abbrev Word := SolidCore.Solidity.Shared.Word
abbrev Byte := Nat
abbrev Name := String

def internalFunctionPointerPanicName : Name :=
  "__solidcore_internal_function_pointer_panic"

def internalFunctionPointerPanicCode : Word := 0x51

structure SourceSpan where
  file : Option String := none
  startByte : Nat := 0
  stopByte : Nat := 0
  deriving Repr

inductive Visibility where
  | public_
  | private_
  | internal_
  | external_
  deriving Repr, BEq

inductive StateMutability where
  | pure
  | view
  | nonpayable
  | payable
  deriving Repr, BEq

inductive DataLocation where
  | storage
  | memory
  | calldata
  deriving Repr, BEq

inductive ContractKind where
  | contract
  | interface
  | library
  deriving Repr, BEq

inductive FunctionKind where
  | function
  | constructor
  | receive
  | fallback
  deriving Repr, BEq

inductive VarMutability where
  | mutable
  | transient
  | constant
  | immutable
  deriving Repr, BEq

structure Path where
  segments : List Name
  deriving Repr, BEq

inductive Ty where
  | bool
  | address : Bool -> Ty
  | uint : Nat -> Ty
  | int : Nat -> Ty
  | fixed : Nat -> Nat -> Ty
  | ufixed : Nat -> Nat -> Ty
  | bytesN : Nat -> Ty
  | bytes
  | string
  | fixedBytes : Nat -> Ty
  | array : Ty -> Option Nat -> Ty
  | mapping : Ty -> Ty -> Ty
  | tuple : List Ty -> Ty
  | struct : Path -> List Ty -> Ty
  | user : Path -> Ty
  -- BUG#6 (library-qualified signatures): the resolved enum type carries its
  -- CANONICAL (declaring-scope-qualified) source path alongside the member
  -- bound. solc renders enum params in public/external LIBRARY signatures by
  -- canonical name (`isOff(Lib.Mode)`), not by the external-ABI `uint8` form.
  | enum : Path -> Nat -> Ty
  | functionWithLocations :
      List Ty -> List (Option DataLocation) ->
      List Ty -> List (Option DataLocation) ->
      StateMutability -> Visibility -> Ty
  deriving Repr

mutual

/-- Structural equality of types, field by field as `deriving BEq` compares them.
Written out because the derived instance of a nested inductive is a `partial` def,
which the kernel cannot unfold. -/
def Ty.beq : Ty -> Ty -> Bool
  | .bool, .bool => true
  | .address a, .address b => a == b
  | .uint a, .uint b => a == b
  | .int a, .int b => a == b
  | .fixed a b, .fixed c d => a == c && b == d
  | .ufixed a b, .ufixed c d => a == c && b == d
  | .bytesN a, .bytesN b => a == b
  | .bytes, .bytes => true
  | .string, .string => true
  | .fixedBytes a, .fixedBytes b => a == b
  | .array a n, .array b m => Ty.beq a b && n == m
  | .mapping a b, .mapping c d => Ty.beq a c && Ty.beq b d
  | .tuple as, .tuple bs => Ty.beqList as bs
  | .struct p as, .struct q bs => p == q && Ty.beqList as bs
  | .user p, .user q => p == q
  | .enum p n, .enum q m => p == q && n == m
  | .functionWithLocations a b c d e f, .functionWithLocations a' b' c' d' e' f' =>
      Ty.beqList a a' && b == b' && Ty.beqList c c' && d == d' && e == e' && f == f'
  | _, _ => false

/-- `Ty.beq` on lists, as `List`'s `BEq` compares them. -/
def Ty.beqList : List Ty -> List Ty -> Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false

end

instance : BEq Ty := ⟨Ty.beq⟩

/-! ### A flat print of types

`Ty.reprFlat` prints a type as its derived `Repr` instance does when the print fits on
one line, by structural recursion, so the kernel can evaluate it (the derived instance
goes through `Std.Format.pretty`, a `partial` def). -/

/-- The print of a constructor applied to the prints of its arguments, in parentheses in
argument position (even with no arguments), as derived `Repr` instances print one on a
single line. -/
def Ty.reprApp (ctor : String) (args : List String) (arg : Bool) : String :=
  let s := ctor ++ String.join (args.map (" " ++ ·))
  if arg then "(" ++ s ++ ")" else s

/-- A list's elements, as `List.repr` prints them on one line. -/
def Ty.reprBrackets (items : List String) : String :=
  "[" ++ ", ".intercalate items ++ "]"

/-- A path, as its derived `Repr` prints it on one line. -/
def Ty.reprPath (p : Path) : String :=
  "{ segments := " ++ Ty.reprBrackets (p.segments.map String.quote) ++ " }"

/-- An optional data location, as `Option`'s `Repr` prints it on one line. -/
def Ty.reprLocation : Option DataLocation -> String
  | none => "none"
  | some .storage => "some (SolidCore.Solidity.DataLocation.storage)"
  | some .memory => "some (SolidCore.Solidity.DataLocation.memory)"
  | some .calldata => "some (SolidCore.Solidity.DataLocation.calldata)"

/-- A state mutability, as its derived `Repr` prints it. -/
def Ty.reprMutability : StateMutability -> String
  | .pure => "SolidCore.Solidity.StateMutability.pure"
  | .view => "SolidCore.Solidity.StateMutability.view"
  | .nonpayable => "SolidCore.Solidity.StateMutability.nonpayable"
  | .payable => "SolidCore.Solidity.StateMutability.payable"

/-- A visibility, as its derived `Repr` prints it. -/
def Ty.reprVisibility : Visibility -> String
  | .public_ => "SolidCore.Solidity.Visibility.public_"
  | .private_ => "SolidCore.Solidity.Visibility.private_"
  | .internal_ => "SolidCore.Solidity.Visibility.internal_"
  | .external_ => "SolidCore.Solidity.Visibility.external_"

mutual

/-- A type, as its derived `Repr` prints it on one line; `arg` is argument position. -/
def Ty.reprFlat : Ty -> Bool -> String
  | .bool, arg => Ty.reprApp "SolidCore.Solidity.Ty.bool" [] arg
  | .address b, arg => Ty.reprApp "SolidCore.Solidity.Ty.address" [toString b] arg
  | .uint n, arg => Ty.reprApp "SolidCore.Solidity.Ty.uint" [toString n] arg
  | .int n, arg => Ty.reprApp "SolidCore.Solidity.Ty.int" [toString n] arg
  | .fixed m n, arg => Ty.reprApp "SolidCore.Solidity.Ty.fixed" [toString m, toString n] arg
  | .ufixed m n, arg => Ty.reprApp "SolidCore.Solidity.Ty.ufixed" [toString m, toString n] arg
  | .bytesN n, arg => Ty.reprApp "SolidCore.Solidity.Ty.bytesN" [toString n] arg
  | .bytes, arg => Ty.reprApp "SolidCore.Solidity.Ty.bytes" [] arg
  | .string, arg => Ty.reprApp "SolidCore.Solidity.Ty.string" [] arg
  | .fixedBytes n, arg => Ty.reprApp "SolidCore.Solidity.Ty.fixedBytes" [toString n] arg
  | .array t n, arg =>
      Ty.reprApp "SolidCore.Solidity.Ty.array"
        [Ty.reprFlat t true, match n with | none => "none" | some n => "(some " ++ toString n ++ ")"] arg
  | .mapping k v, arg =>
      Ty.reprApp "SolidCore.Solidity.Ty.mapping" [Ty.reprFlat k true, Ty.reprFlat v true] arg
  | .tuple ts, arg => Ty.reprApp "SolidCore.Solidity.Ty.tuple" [Ty.reprFlatList ts] arg
  | .struct p ts, arg =>
      Ty.reprApp "SolidCore.Solidity.Ty.struct" [Ty.reprPath p, Ty.reprFlatList ts] arg
  | .user p, arg => Ty.reprApp "SolidCore.Solidity.Ty.user" [Ty.reprPath p] arg
  | .enum p n, arg => Ty.reprApp "SolidCore.Solidity.Ty.enum" [Ty.reprPath p, toString n] arg
  | .functionWithLocations ps pl rs rl m v, arg =>
      Ty.reprApp "SolidCore.Solidity.Ty.functionWithLocations"
        [Ty.reprFlatList ps, Ty.reprBrackets (pl.map Ty.reprLocation), Ty.reprFlatList rs,
          Ty.reprBrackets (rl.map Ty.reprLocation), "(" ++ Ty.reprMutability m ++ ")", "(" ++ Ty.reprVisibility v ++ ")"] arg

/-- A list of types, as `List.repr` prints it on one line. -/
def Ty.reprFlatList (ts : List Ty) : String :=
  "[" ++ Ty.reprFlatItems ts ++ "]"

/-- The elements of a list of types, separated by `, `. -/
def Ty.reprFlatItems : List Ty -> String
  | [] => ""
  | [t] => Ty.reprFlat t false
  | t :: ts => Ty.reprFlat t false ++ ", " ++ Ty.reprFlatItems ts

end

/-- `toString (repr ts)`, by the flat print when it is short enough to fit on one line
(`Std.Format.defWidth` is 120 columns) and so is the derived print itself. -/
def Ty.reprListString (ts : List Ty) : String :=
  let s := Ty.reprFlatList ts
  if s.length < 100 then s else toString (repr ts)

def Ty.function (params returns : List Ty)
    (mutability : StateMutability) (visibility : Visibility) : Ty :=
  Ty.functionWithLocations params (List.replicate params.length none)
    returns (List.replicate returns.length none) mutability visibility

def Ty.validFixedPointShape (bits decimals : Nat) : Bool :=
  8 <= bits && bits <= 256 && bits % 8 == 0 && decimals <= 80

def Ty.fixedPointImplicitlyConvertible
    (actualSigned : Bool) (actualBits actualDecimals : Nat)
    (expectedSigned : Bool) (expectedBits expectedDecimals : Nat) : Bool :=
  actualDecimals <= expectedDecimals &&
    if actualSigned == expectedSigned then
      actualBits <= expectedBits
    else
      !actualSigned && expectedSigned && actualBits < expectedBits

def Ty.commonFixedPoint?
    (leftSigned : Bool) (leftBits leftDecimals : Nat)
    (rightSigned : Bool) (rightBits rightDecimals : Nat) : Option Ty :=
  let decimals := max leftDecimals rightDecimals
  if leftSigned == rightSigned then
    let bits := max leftBits rightBits
    if Ty.validFixedPointShape bits decimals then
      if leftSigned then some (Ty.fixed bits decimals)
      else some (Ty.ufixed bits decimals)
    else
      none
  else
    let signedBits := if leftSigned then leftBits else rightBits
    let unsignedBits := if leftSigned then rightBits else leftBits
    let bits := max signedBits (unsignedBits + 8)
    if Ty.validFixedPointShape bits decimals then
      some (Ty.fixed bits decimals)
    else
      none

structure Parameter where
  name : Option Name := none
  ty : Ty
  location : Option DataLocation := none
  deriving Repr

inductive UnitDenomination where
  | wei
  | gwei
  | ether
  | seconds
  | minutes
  | hours
  | days
  | weeks
  deriving Repr, BEq

namespace UnitDenomination

def factor : UnitDenomination -> Nat
  | UnitDenomination.wei => 1
  | UnitDenomination.gwei => 1000000000
  | UnitDenomination.ether => 1000000000000000000
  | UnitDenomination.seconds => 1
  | UnitDenomination.minutes => 60
  | UnitDenomination.hours => 3600
  | UnitDenomination.days => 86400
  | UnitDenomination.weeks => 604800

end UnitDenomination

inductive Literal where
  | bool : Bool -> Literal
  | number : String -> Literal
  | unitNumber : String -> UnitDenomination -> Literal
  | string : String -> Literal
  | hexString : String -> Literal
  | unicodeString : String -> Literal
  | address : Word -> Literal
  | bytes : List Byte -> Literal
  deriving Repr

inductive UnaryOp where
  | logicalNot
  | bitNot
  | neg
  | delete
  | preIncrement
  | preDecrement
  | postIncrement
  | postDecrement
  deriving Repr, BEq

inductive BinaryOp where
  | add
  | sub
  | mul
  | div
  | mod
  | exp
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | shr
  | sar
  | lt
  | gt
  | le
  | ge
  | eq
  | ne
  | boolAnd
  | boolOr
  deriving Repr, BEq

inductive UsingOperator where
  | unary : UnaryOp -> UsingOperator
  | binary : BinaryOp -> UsingOperator
  deriving Repr, BEq

inductive AssignOp where
  | assign
  | addAssign
  | subAssign
  | mulAssign
  | divAssign
  | modAssign
  | bitAndAssign
  | bitOrAssign
  | bitXorAssign
  | shlAssign
  | shrAssign
  | sarAssign
  deriving Repr

mutual

inductive Expr where
  | literal : Literal -> Expr
  | ident : Name -> Expr
  | typeName : Ty -> Expr
  | member : Expr -> Name -> Expr
  | index : Expr -> Expr -> Expr
  | slice : Expr -> Option Expr -> Option Expr -> Expr
  | call : Expr -> List Arg -> Expr
  | callWithOptions : Expr -> List CallOption -> List Arg -> Expr
  | newExpr : Ty -> List Arg -> Expr
  | tuple : List TupleItem -> Expr
  | array : List Expr -> Expr
  | enumFromUInt : Word -> Expr -> Expr
  | unary : UnaryOp -> Expr -> Expr
  | binary : BinaryOp -> Expr -> Expr -> Expr
  | ternary : Expr -> Expr -> Expr -> Expr
  | assign : Expr -> AssignOp -> Expr -> Expr
  | payableConversion : Expr -> Expr
  deriving Repr

inductive Arg where
  | positional : Expr -> Arg
  | named : Name -> Expr -> Arg
  deriving Repr

inductive CallOption where
  | named : Name -> Expr -> CallOption
  deriving Repr

inductive TupleItem where
  | hole
  | value : Expr -> TupleItem
  deriving Repr

end

structure VarBinding where
  name : Option Name := none
  ty : Option Ty := none
  location : Option DataLocation := none
  deriving Repr

mutual

inductive Stmt where
  | empty
  | block : List Stmt -> Stmt
  | varDecl : List VarBinding -> Option Expr -> Stmt
  | expr : Expr -> Stmt
  | ifElse : Expr -> Stmt -> Option Stmt -> Stmt
  | whileLoop : Expr -> Stmt -> Stmt
  | doWhile : Stmt -> Expr -> Stmt
  | forLoop : Option Stmt -> Option Expr -> Option Expr -> Stmt -> Stmt
  | tryCatch : Expr -> List CatchClause -> Stmt
  | tryCatchReturns : Expr -> List Parameter -> Stmt -> List CatchClause -> Stmt
  | emitEvent : Expr -> Stmt
  | revertCall : Expr -> Stmt
  | returnValues : Option Expr -> Stmt
  | break
  | continue
  | unchecked : Stmt -> Stmt
  | inlineAssembly : String -> Stmt
  | modifierPlaceholder
  deriving Repr

inductive CatchClause where
  | clause : Option Name -> List Parameter -> Stmt -> CatchClause
  deriving Repr

end

structure ModifierInvocation where
  target : Path
  args : List Arg := []
  -- Whether the source wrote an argument list at all. solc's AST distinguishes
  -- `arguments == null` (bare modifier-style name, e.g. base `B`) from
  -- `arguments == []` (empty parens, `B()`). A bare modifier-style
  -- base-constructor call is a declaration error (solc 1563); `B()` is fine.
  -- Defaults to `true` so hand-built ASTs behave like an explicit arg list.
  hasArgList : Bool := true
  deriving Repr

structure OverrideSpecifier where
  bases : List Path := []
  deriving Repr

structure StateVarDecl where
  name : Name
  ty : Ty
  visibility : Option Visibility := none
  mutability : VarMutability := VarMutability.mutable
  override? : Option OverrideSpecifier := none
  init : Option Expr := none
  deriving Repr

structure FunctionDecl where
  kind : FunctionKind := FunctionKind.function
  name : Option Name := none
  params : List Parameter := []
  returns : List Parameter := []
  visibility : Option Visibility := none
  mutability : StateMutability := StateMutability.nonpayable
  virtual : Bool := false
  override? : Option OverrideSpecifier := none
  modifiers : List ModifierInvocation := []
  body : Option Stmt := none
  deriving Repr

structure ModifierDecl where
  name : Name
  params : List Parameter := []
  virtual : Bool := false
  override? : Option OverrideSpecifier := none
  body : Option Stmt := none
  -- Set during whole-contract elaboration to the contract that DECLARES this
  -- modifier (its position in the C3 linearization). Used to resolve a
  -- statically QUALIFIED modifier invocation `Base.m` (solc
  -- `VirtualLookup::Static`) to the named base's own modifier, rather than the
  -- most-derived override that name-first lookup would pick. `none` on
  -- freshly-imported/hand-built decls; stamped by
  -- `ContractDecl.directModifiersStamped`.
  declaringContract : Option Name := none
  deriving Repr

structure EventParam where
  name : Option Name := none
  ty : Ty
  indexed : Bool := false
  deriving Repr

structure EventDecl where
  name : Name
  params : List EventParam := []
  anonymous : Bool := false
  deriving Repr

structure ErrorDecl where
  name : Name
  params : List Parameter := []
  deriving Repr

structure StructField where
  name : Name
  ty : Ty
  deriving Repr

structure StructDecl where
  name : Name
  fields : List StructField := []
  -- Declaring contract/library scope, stamped when the decl enters a
  -- `StructEnv` (BUG#6): recovers solc's canonical name (`Lib.S`) for
  -- library-qualified signature rendering. `none` for file-level structs.
  declScope? : Option Name := none
  deriving Repr

structure EnumDecl where
  name : Name
  cases : List Name := []
  -- Declaring contract/library scope, stamped when the decl enters an
  -- `EnumEnv` (BUG#6): recovers solc's canonical name (`Lib.Mode`) for
  -- library-qualified signature rendering. `none` for file-level enums.
  declScope? : Option Name := none
  deriving Repr

structure UserValueTypeDecl where
  name : Name
  underlying : Ty
  deriving Repr

structure UsingFunction where
  function : Path
  operator? : Option UsingOperator := none
  deriving Repr

structure UsingDecl where
  library : Path
  functions : List UsingFunction := []
  target : Option Ty := none
  global : Bool := false
  deriving Repr

structure BaseSpecifier where
  base : Path
  args : List Arg := []
  deriving Repr

inductive ContractItem where
  | stateVar : StateVarDecl -> ContractItem
  | function : FunctionDecl -> ContractItem
  | modifierDecl : ModifierDecl -> ContractItem
  | eventDecl : EventDecl -> ContractItem
  | errorDecl : ErrorDecl -> ContractItem
  | structDecl : StructDecl -> ContractItem
  | enumDecl : EnumDecl -> ContractItem
  | userValueTypeDecl : UserValueTypeDecl -> ContractItem
  | usingDecl : UsingDecl -> ContractItem
  deriving Repr

structure ContractDecl where
  kind : ContractKind := ContractKind.contract
  name : Name
  abstract : Bool := false
  layoutBase : Option Expr := none
  bases : List BaseSpecifier := []
  items : List ContractItem := []
  deriving Repr

inductive SourceItem where
  | pragma : Name -> String -> SourceItem
  | importPath : String -> Option Name -> SourceItem
  | contract : ContractDecl -> SourceItem
  | freeFunction : FunctionDecl -> SourceItem
  | freeConstant : StateVarDecl -> SourceItem
  | freeEvent : EventDecl -> SourceItem
  | freeError : ErrorDecl -> SourceItem
  | freeStruct : StructDecl -> SourceItem
  | freeEnum : EnumDecl -> SourceItem
  | freeUserValueType : UserValueTypeDecl -> SourceItem
  | usingDecl : UsingDecl -> SourceItem
  deriving Repr

structure SourceUnit where
  items : List SourceItem := []
  deriving Repr

inductive Behavior where
  | stopped
  | returnedWord : Word -> Behavior
  deriving Repr

end Solidity
end SolidCore
