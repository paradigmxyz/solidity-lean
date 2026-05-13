import SolidCore.Solidity.ABI
import SharedSemantics.Precompile
import SharedSemantics.Word

namespace SolidCore
namespace Spine
namespace L00_SourceSolidity

abbrev Word := SharedSemantics.Word
abbrev Byte := Nat
abbrev Name := String

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
  | bytesN : Nat -> Ty
  | bytes
  | string
  | fixedBytes : Nat -> Ty
  | array : Ty -> Option Nat -> Ty
  | mapping : Ty -> Ty -> Ty
  | tuple : List Ty -> Ty
  | user : Path -> Ty
  | function : List Ty -> List Ty -> StateMutability -> Visibility -> Ty
  deriving Repr, BEq

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
  deriving Repr

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
  deriving Repr

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
  deriving Repr

structure EnumDecl where
  name : Name
  cases : List Name := []
  deriving Repr

structure UserValueTypeDecl where
  name : Name
  underlying : Ty
  deriving Repr

structure UsingDecl where
  library : Path
  target : Option Ty := none
  global : Bool := false
  deriving Repr

structure BaseSpecifier where
  base : Path
  args : List Expr := []
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
  bases : List BaseSpecifier := []
  items : List ContractItem := []
  deriving Repr

inductive SourceItem where
  | pragma : Name -> String -> SourceItem
  | importPath : String -> Option Name -> SourceItem
  | contract : ContractDecl -> SourceItem
  | freeFunction : FunctionDecl -> SourceItem
  | freeConstant : StateVarDecl -> SourceItem
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

/-
Executable source semantics exposed by L00.

The broad AST above intentionally represents pre-validity Solidity. The
interpreter reused here is the existing executable Solidity source core in
`SolidCore.Solidity.Source`: it already models checked/unchecked arithmetic,
locals, storage slots, arrays/bytes indexing, events, custom errors, returns,
reverts, loops, function calls, and ABI entry behavior for the executable
fragment. The translation functions below are deliberately optional and
feature-by-feature: validity checking and unsupported Solidity constructs stay
separate from parser/import success and from later compiler lowering.
-/
namespace Executable

abbrev CoreTy := SolidCore.Solidity.Source.Ty
abbrev CoreValue := SolidCore.Solidity.Source.Value
abbrev CoreExpr := SolidCore.Solidity.Source.Expr
abbrev CoreLValue := SolidCore.Solidity.Source.LValue
abbrev CoreStmt := SolidCore.Solidity.Source.Stmt
abbrev CoreTryCatchClause := SolidCore.Solidity.Source.TryCatchClause
abbrev CoreContext := SolidCore.Solidity.Source.Context
abbrev CoreRuntime := SolidCore.Solidity.Source.Runtime
abbrev CoreState := SolidCore.Solidity.Source.State
abbrev CoreResult := SolidCore.Solidity.Source.Result
abbrev CoreRevertData := SolidCore.Solidity.Source.RevertData
abbrev CoreFunctionDef := SolidCore.Solidity.Source.FunctionDef
abbrev CoreContract := SolidCore.Solidity.Source.Contract
abbrev CoreCallResult := SolidCore.Solidity.Source.CallResult
abbrev CoreBindingDecl := SolidCore.Solidity.Source.BindingDecl
abbrev CoreStorageField := SolidCore.Solidity.Source.StorageField
abbrev CoreImmutableField := SolidCore.Solidity.Source.ImmutableField
abbrev CoreStorageLayout := SolidCore.Solidity.Source.StorageLayout
abbrev CoreEventDecl := SolidCore.Solidity.Source.EventDecl
abbrev CoreErrorDecl := SolidCore.Solidity.Source.ErrorDecl
abbrev CoreLowLevelCallKind := SolidCore.Solidity.Source.LowLevelCallKind
abbrev SourceModifierDecl :=
  _root_.SolidCore.Spine.L00_SourceSolidity.ModifierDecl
abbrev SourceModifierInvocation :=
  _root_.SolidCore.Spine.L00_SourceSolidity.ModifierInvocation

def pathLast? (path : Path) : Option Name :=
  path.segments.reverse.head?

def pathMatchesName (path : Path) (name : Name) : Bool :=
  match pathLast? path with
  | some candidate => candidate == name
  | none => false

def nameIn (name : Name) : List Name -> Bool
  | [] => false
  | candidate :: rest => candidate == name || nameIn name rest

def namesUnique : List Name -> Bool
  | [] => true
  | name :: rest => !nameIn name rest && namesUnique rest

def immutableNameTag (name : Name) : Name :=
  "__immutable:" ++ name

def stateNameIsStorage (name : Name) (stateNames : List Name) : Bool :=
  nameIn name stateNames

def stateNameIsImmutable (name : Name) (stateNames : List Name) : Bool :=
  nameIn (immutableNameTag name) stateNames

def stateNamesFrom (storageVars immutableVars : List StateVarDecl) :
    List Name :=
  storageVars.map StateVarDecl.name ++
    immutableVars.map (fun decl => immutableNameTag decl.name)

abbrev ConstantEnv := List (Name × Expr)

def ConstantEnv.lookup? (env : ConstantEnv) (name : Name) : Option Expr :=
  match env with
  | [] => none
  | (candidate, expr) :: rest =>
      if candidate == name then
        some expr
      else
        ConstantEnv.lookup? rest name

mutual

def Expr.inlineConstantsFuel : Nat -> ConstantEnv -> Expr -> Expr
  | 0, _, expr => expr
  | fuel + 1, constants, expr =>
      let inline := Expr.inlineConstantsFuel fuel constants
      let inlineArg := Arg.inlineConstantsFuel fuel constants
      let inlineOption := CallOption.inlineConstantsFuel fuel constants
      let inlineTupleItem := TupleItem.inlineConstantsFuel fuel constants
      match expr with
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name =>
          match ConstantEnv.lookup? constants name with
          | some replacement => inline replacement
          | none => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (inline base) member
      | Expr.index base index => Expr.index (inline base) (inline index)
      | Expr.slice base start stop =>
          Expr.slice (inline base) (start.map inline) (stop.map inline)
      | Expr.call fn args =>
          Expr.call (inline fn) (args.map inlineArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (inline fn)
            (options.map inlineOption) (args.map inlineArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map inlineArg)
      | Expr.tuple items => Expr.tuple (items.map inlineTupleItem)
      | Expr.array exprs => Expr.array (exprs.map inline)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (inline inner)
      | Expr.unary op inner => Expr.unary op (inline inner)
      | Expr.binary op lhs rhs => Expr.binary op (inline lhs) (inline rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (inline cond) (inline thenExpr) (inline elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (inline lhs) op (inline rhs)
      | Expr.payableConversion inner => Expr.payableConversion (inline inner)

def Arg.inlineConstantsFuel : Nat -> ConstantEnv -> Arg -> Arg
  | 0, _, arg => arg
  | fuel + 1, constants, arg =>
      let inline := Expr.inlineConstantsFuel fuel constants
      match arg with
      | Arg.positional expr => Arg.positional (inline expr)
      | Arg.named name expr => Arg.named name (inline expr)

def CallOption.inlineConstantsFuel :
    Nat -> ConstantEnv -> CallOption -> CallOption
  | 0, _, option => option
  | fuel + 1, constants, option =>
      let inline := Expr.inlineConstantsFuel fuel constants
      match option with
      | CallOption.named name expr => CallOption.named name (inline expr)

def TupleItem.inlineConstantsFuel :
    Nat -> ConstantEnv -> TupleItem -> TupleItem
  | 0, _, item => item
  | fuel + 1, constants, item =>
      let inline := Expr.inlineConstantsFuel fuel constants
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (inline expr)

end

def defaultInlineConstantsFuel : Nat := 1024

def Expr.inlineConstants (constants : ConstantEnv) (expr : Expr) : Expr :=
  Expr.inlineConstantsFuel defaultInlineConstantsFuel constants expr

def Arg.inlineConstants (constants : ConstantEnv) (arg : Arg) : Arg :=
  Arg.inlineConstantsFuel defaultInlineConstantsFuel constants arg

def CallOption.inlineConstants (constants : ConstantEnv)
    (option : CallOption) : CallOption :=
  CallOption.inlineConstantsFuel defaultInlineConstantsFuel constants option

def TupleItem.inlineConstants (constants : ConstantEnv)
    (item : TupleItem) : TupleItem :=
  TupleItem.inlineConstantsFuel defaultInlineConstantsFuel constants item

mutual

def Stmt.inlineConstantsFuel : Nat -> ConstantEnv -> Stmt -> Stmt
  | 0, _, stmt => stmt
  | fuel + 1, constants, stmt =>
      let inlineExpr := Expr.inlineConstantsFuel fuel constants
      let inlineStmt := Stmt.inlineConstantsFuel fuel constants
      let inlineClause := CatchClause.inlineConstantsFuel fuel constants
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body => Stmt.block (body.map inlineStmt)
      | Stmt.varDecl bindings init =>
          Stmt.varDecl bindings (init.map inlineExpr)
      | Stmt.expr expr => Stmt.expr (inlineExpr expr)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (inlineExpr cond) (inlineStmt thenBranch)
            (elseBranch.map inlineStmt)
      | Stmt.whileLoop cond body =>
          Stmt.whileLoop (inlineExpr cond) (inlineStmt body)
      | Stmt.doWhile body cond =>
          Stmt.doWhile (inlineStmt body) (inlineExpr cond)
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map inlineStmt) (cond.map inlineExpr)
            (post.map inlineExpr) (inlineStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch (inlineExpr expr) (clauses.map inlineClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          Stmt.tryCatchReturns (inlineExpr expr) returns
            (inlineStmt success) (clauses.map inlineClause)
      | Stmt.emitEvent expr => Stmt.emitEvent (inlineExpr expr)
      | Stmt.revertCall expr => Stmt.revertCall (inlineExpr expr)
      | Stmt.returnValues expr? => Stmt.returnValues (expr?.map inlineExpr)
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (inlineStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.inlineConstantsFuel :
    Nat -> ConstantEnv -> CatchClause -> CatchClause
  | 0, _, clause => clause
  | fuel + 1, constants, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name params
            (Stmt.inlineConstantsFuel fuel constants body)

end

def Stmt.inlineConstants (constants : ConstantEnv) (stmt : Stmt) : Stmt :=
  Stmt.inlineConstantsFuel defaultInlineConstantsFuel constants stmt

def CatchClause.inlineConstants (constants : ConstantEnv)
    (clause : CatchClause) : CatchClause :=
  CatchClause.inlineConstantsFuel defaultInlineConstantsFuel constants clause

def ModifierInvocation.inlineConstants (constants : ConstantEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with args := invocation.args.map (Arg.inlineConstants constants) }

def BaseSpecifier.inlineConstants (constants : ConstantEnv)
    (specifier : BaseSpecifier) : BaseSpecifier :=
  { specifier with args := specifier.args.map (Expr.inlineConstants constants) }

def FunctionDecl.inlineConstants (constants : ConstantEnv)
    (decl : FunctionDecl) : FunctionDecl :=
  { decl with
    modifiers := decl.modifiers.map
      (ModifierInvocation.inlineConstants constants)
    body := decl.body.map (Stmt.inlineConstants constants) }

def ModifierDecl.inlineConstants (constants : ConstantEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  { decl with body := decl.body.map (Stmt.inlineConstants constants) }

def superHelperName (contractName functionName : Name) : Name :=
  "__super_" ++ contractName ++ "_" ++ functionName

def baseHelperName (contractName functionName : Name) : Name :=
  "__base_" ++ contractName ++ "_" ++ functionName

mutual

def Expr.rewriteSuperCallsFuel (contractName : Name) : Nat -> Expr -> Expr
  | 0, expr => expr
  | fuel + 1, expr =>
      let rewrite := Expr.rewriteSuperCallsFuel contractName fuel
      let rewriteArg := Arg.rewriteSuperCallsFuel contractName fuel
      let rewriteOption := CallOption.rewriteSuperCallsFuel contractName fuel
      let rewriteTupleItem := TupleItem.rewriteSuperCallsFuel contractName fuel
      match expr with
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (rewrite base) member
      | Expr.index base index => Expr.index (rewrite base) (rewrite index)
      | Expr.slice base start stop =>
          Expr.slice (rewrite base) (start.map rewrite) (stop.map rewrite)
      | Expr.call (Expr.member (Expr.ident "super") member) args =>
          Expr.call (Expr.ident (superHelperName contractName member))
            (args.map rewriteArg)
      | Expr.call fn args => Expr.call (rewrite fn) (args.map rewriteArg)
      | Expr.callWithOptions (Expr.member (Expr.ident "super") member)
          options args =>
          Expr.callWithOptions (Expr.ident (superHelperName contractName member))
            (options.map rewriteOption) (args.map rewriteArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (rewrite fn) (options.map rewriteOption)
            (args.map rewriteArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map rewriteArg)
      | Expr.tuple items => Expr.tuple (items.map rewriteTupleItem)
      | Expr.array exprs => Expr.array (exprs.map rewrite)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (rewrite inner)
      | Expr.unary op inner => Expr.unary op (rewrite inner)
      | Expr.binary op lhs rhs => Expr.binary op (rewrite lhs) (rewrite rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (rewrite cond) (rewrite thenExpr) (rewrite elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (rewrite lhs) op (rewrite rhs)
      | Expr.payableConversion inner => Expr.payableConversion (rewrite inner)

def Arg.rewriteSuperCallsFuel (contractName : Name) : Nat -> Arg -> Arg
  | 0, arg => arg
  | fuel + 1, arg =>
      let rewrite := Expr.rewriteSuperCallsFuel contractName fuel
      match arg with
      | Arg.positional expr => Arg.positional (rewrite expr)
      | Arg.named name expr => Arg.named name (rewrite expr)

def CallOption.rewriteSuperCallsFuel (contractName : Name) :
    Nat -> CallOption -> CallOption
  | 0, option => option
  | fuel + 1, option =>
      let rewrite := Expr.rewriteSuperCallsFuel contractName fuel
      match option with
      | CallOption.named name expr => CallOption.named name (rewrite expr)

def TupleItem.rewriteSuperCallsFuel (contractName : Name) :
    Nat -> TupleItem -> TupleItem
  | 0, item => item
  | fuel + 1, item =>
      let rewrite := Expr.rewriteSuperCallsFuel contractName fuel
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (rewrite expr)

end

def Expr.rewriteSuperCalls (contractName : Name) (expr : Expr) : Expr :=
  Expr.rewriteSuperCallsFuel contractName defaultInlineConstantsFuel expr

def Arg.rewriteSuperCalls (contractName : Name) (arg : Arg) : Arg :=
  Arg.rewriteSuperCallsFuel contractName defaultInlineConstantsFuel arg

def CallOption.rewriteSuperCalls (contractName : Name)
    (option : CallOption) : CallOption :=
  CallOption.rewriteSuperCallsFuel contractName defaultInlineConstantsFuel option

def TupleItem.rewriteSuperCalls (contractName : Name)
    (item : TupleItem) : TupleItem :=
  TupleItem.rewriteSuperCallsFuel contractName defaultInlineConstantsFuel item

mutual

def Stmt.rewriteSuperCallsFuel (contractName : Name) : Nat -> Stmt -> Stmt
  | 0, stmt => stmt
  | fuel + 1, stmt =>
      let rewriteExpr := Expr.rewriteSuperCallsFuel contractName fuel
      let rewriteStmt := Stmt.rewriteSuperCallsFuel contractName fuel
      let rewriteClause := CatchClause.rewriteSuperCallsFuel contractName fuel
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body => Stmt.block (body.map rewriteStmt)
      | Stmt.varDecl bindings init =>
          Stmt.varDecl bindings (init.map rewriteExpr)
      | Stmt.expr expr => Stmt.expr (rewriteExpr expr)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (rewriteExpr cond) (rewriteStmt thenBranch)
            (elseBranch.map rewriteStmt)
      | Stmt.whileLoop cond body =>
          Stmt.whileLoop (rewriteExpr cond) (rewriteStmt body)
      | Stmt.doWhile body cond =>
          Stmt.doWhile (rewriteStmt body) (rewriteExpr cond)
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map rewriteStmt) (cond.map rewriteExpr)
            (post.map rewriteExpr) (rewriteStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch (rewriteExpr expr) (clauses.map rewriteClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          Stmt.tryCatchReturns (rewriteExpr expr) returns
            (rewriteStmt success) (clauses.map rewriteClause)
      | Stmt.emitEvent expr => Stmt.emitEvent (rewriteExpr expr)
      | Stmt.revertCall expr => Stmt.revertCall (rewriteExpr expr)
      | Stmt.returnValues expr? => Stmt.returnValues (expr?.map rewriteExpr)
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (rewriteStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.rewriteSuperCallsFuel (contractName : Name) :
    Nat -> CatchClause -> CatchClause
  | 0, clause => clause
  | fuel + 1, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name params
            (Stmt.rewriteSuperCallsFuel contractName fuel body)

end

def Stmt.rewriteSuperCalls (contractName : Name) (stmt : Stmt) : Stmt :=
  Stmt.rewriteSuperCallsFuel contractName defaultInlineConstantsFuel stmt

def CatchClause.rewriteSuperCalls (contractName : Name)
    (clause : CatchClause) : CatchClause :=
  CatchClause.rewriteSuperCallsFuel contractName defaultInlineConstantsFuel clause

def FunctionDecl.asSuperHelper? (contractName : Name)
    (decl : FunctionDecl) : Option FunctionDecl :=
  match decl.name with
  | some name => some { decl with name := some (superHelperName contractName name) }
  | none => none

def FunctionDecl.superHelpers (contractName : Name) (decls : List FunctionDecl) :
    List FunctionDecl :=
  decls.filterMap (FunctionDecl.asSuperHelper? contractName)

mutual

def Expr.rewriteBaseCallsFuel (baseNames : List Name) :
    Nat -> Expr -> Expr
  | 0, expr => expr
  | fuel + 1, expr =>
      let rewrite := Expr.rewriteBaseCallsFuel baseNames fuel
      let rewriteArg := Arg.rewriteBaseCallsFuel baseNames fuel
      let rewriteOption := CallOption.rewriteBaseCallsFuel baseNames fuel
      let rewriteTupleItem := TupleItem.rewriteBaseCallsFuel baseNames fuel
      match expr with
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (rewrite base) member
      | Expr.index base index => Expr.index (rewrite base) (rewrite index)
      | Expr.slice base start stop =>
          Expr.slice (rewrite base) (start.map rewrite) (stop.map rewrite)
      | Expr.call (Expr.member (Expr.ident baseName) member) args =>
          if nameIn baseName baseNames then
            Expr.call (Expr.ident (baseHelperName baseName member))
              (args.map rewriteArg)
          else
            Expr.call (Expr.member (Expr.ident baseName) member)
              (args.map rewriteArg)
      | Expr.call fn args => Expr.call (rewrite fn) (args.map rewriteArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (rewrite fn) (options.map rewriteOption)
            (args.map rewriteArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map rewriteArg)
      | Expr.tuple items => Expr.tuple (items.map rewriteTupleItem)
      | Expr.array exprs => Expr.array (exprs.map rewrite)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (rewrite inner)
      | Expr.unary op inner => Expr.unary op (rewrite inner)
      | Expr.binary op lhs rhs => Expr.binary op (rewrite lhs) (rewrite rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (rewrite cond) (rewrite thenExpr) (rewrite elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (rewrite lhs) op (rewrite rhs)
      | Expr.payableConversion inner => Expr.payableConversion (rewrite inner)

def Arg.rewriteBaseCallsFuel (baseNames : List Name) :
    Nat -> Arg -> Arg
  | 0, arg => arg
  | fuel + 1, arg =>
      let rewrite := Expr.rewriteBaseCallsFuel baseNames fuel
      match arg with
      | Arg.positional expr => Arg.positional (rewrite expr)
      | Arg.named name expr => Arg.named name (rewrite expr)

def CallOption.rewriteBaseCallsFuel (baseNames : List Name) :
    Nat -> CallOption -> CallOption
  | 0, option => option
  | fuel + 1, option =>
      let rewrite := Expr.rewriteBaseCallsFuel baseNames fuel
      match option with
      | CallOption.named name expr => CallOption.named name (rewrite expr)

def TupleItem.rewriteBaseCallsFuel (baseNames : List Name) :
    Nat -> TupleItem -> TupleItem
  | 0, item => item
  | fuel + 1, item =>
      let rewrite := Expr.rewriteBaseCallsFuel baseNames fuel
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (rewrite expr)

end

def Expr.rewriteBaseCalls (baseNames : List Name) (expr : Expr) : Expr :=
  Expr.rewriteBaseCallsFuel baseNames defaultInlineConstantsFuel expr

def Arg.rewriteBaseCalls (baseNames : List Name) (arg : Arg) : Arg :=
  Arg.rewriteBaseCallsFuel baseNames defaultInlineConstantsFuel arg

def CallOption.rewriteBaseCalls (baseNames : List Name)
    (option : CallOption) : CallOption :=
  CallOption.rewriteBaseCallsFuel baseNames defaultInlineConstantsFuel option

def TupleItem.rewriteBaseCalls (baseNames : List Name)
    (item : TupleItem) : TupleItem :=
  TupleItem.rewriteBaseCallsFuel baseNames defaultInlineConstantsFuel item

mutual

def Stmt.rewriteBaseCallsFuel (baseNames : List Name) :
    Nat -> Stmt -> Stmt
  | 0, stmt => stmt
  | fuel + 1, stmt =>
      let rewriteExpr := Expr.rewriteBaseCallsFuel baseNames fuel
      let rewriteStmt := Stmt.rewriteBaseCallsFuel baseNames fuel
      let rewriteClause := CatchClause.rewriteBaseCallsFuel baseNames fuel
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body => Stmt.block (body.map rewriteStmt)
      | Stmt.varDecl bindings init =>
          Stmt.varDecl bindings (init.map rewriteExpr)
      | Stmt.expr expr => Stmt.expr (rewriteExpr expr)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (rewriteExpr cond) (rewriteStmt thenBranch)
            (elseBranch.map rewriteStmt)
      | Stmt.whileLoop cond body =>
          Stmt.whileLoop (rewriteExpr cond) (rewriteStmt body)
      | Stmt.doWhile body cond =>
          Stmt.doWhile (rewriteStmt body) (rewriteExpr cond)
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map rewriteStmt) (cond.map rewriteExpr)
            (post.map rewriteExpr) (rewriteStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch (rewriteExpr expr) (clauses.map rewriteClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          Stmt.tryCatchReturns (rewriteExpr expr) returns
            (rewriteStmt success) (clauses.map rewriteClause)
      | Stmt.emitEvent expr => Stmt.emitEvent (rewriteExpr expr)
      | Stmt.revertCall expr => Stmt.revertCall (rewriteExpr expr)
      | Stmt.returnValues expr? => Stmt.returnValues (expr?.map rewriteExpr)
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (rewriteStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.rewriteBaseCallsFuel (baseNames : List Name) :
    Nat -> CatchClause -> CatchClause
  | 0, clause => clause
  | fuel + 1, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name params
            (Stmt.rewriteBaseCallsFuel baseNames fuel body)

end

def Stmt.rewriteBaseCalls (baseNames : List Name) (stmt : Stmt) : Stmt :=
  Stmt.rewriteBaseCallsFuel baseNames defaultInlineConstantsFuel stmt

def CatchClause.rewriteBaseCalls (baseNames : List Name)
    (clause : CatchClause) : CatchClause :=
  CatchClause.rewriteBaseCallsFuel baseNames defaultInlineConstantsFuel clause

def FunctionDecl.asBaseHelper? (contractName : Name)
    (decl : FunctionDecl) : Option FunctionDecl :=
  match decl.name with
  | some name => some { decl with name := some (baseHelperName contractName name) }
  | none => none

def ContractDecl.baseHelpers (decl : ContractDecl) : List FunctionDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.function fn =>
        match fn.kind with
        | FunctionKind.constructor => none
        | _ => FunctionDecl.asBaseHelper? decl.name fn
    | _ => none)

abbrev TypeEnv := List (Name × Ty)

abbrev UserTypeEnv := List (Name × Ty)

abbrev EnumEnv := List (Name × EnumDecl)

abbrev StructEnv := List (Name × StructDecl)

def TypeEnv.lookup? (env : TypeEnv) (name : Name) : Option Ty :=
  match env with
  | [] => none
  | (candidate, ty) :: rest =>
      if candidate == name then
        some ty
      else
        TypeEnv.lookup? rest name

def TypeEnv.extend? (env : TypeEnv) (name? : Option Name)
    (ty? : Option Ty) : TypeEnv :=
  match name?, ty? with
  | some name, some ty => (name, ty) :: env
  | _, _ => env

def UserTypeEnv.lookupName? (env : UserTypeEnv) (name : Name) :
    Option Ty :=
  match env with
  | [] => none
  | (candidate, ty) :: rest =>
      if candidate == name then
        some ty
      else
        UserTypeEnv.lookupName? rest name

def UserTypeEnv.lookup? (env : UserTypeEnv) (path : Path) : Option Ty := do
  let name ← pathLast? path
  UserTypeEnv.lookupName? env name

def UserTypeEnv.extendDecl (env : UserTypeEnv)
    (decl : UserValueTypeDecl) : UserTypeEnv :=
  (decl.name, decl.underlying) :: env

def EnumEnv.lookupName? (env : EnumEnv) (name : Name) :
    Option EnumDecl :=
  match env with
  | [] => none
  | (candidate, decl) :: rest =>
      if candidate == name then
        some decl
      else
        EnumEnv.lookupName? rest name

def EnumEnv.lookup? (env : EnumEnv) (path : Path) : Option EnumDecl := do
  let name ← pathLast? path
  EnumEnv.lookupName? env name

def EnumEnv.extendDecl (env : EnumEnv) (decl : EnumDecl) : EnumEnv :=
  (decl.name, decl) :: env

def StructEnv.lookupName? (env : StructEnv) (name : Name) :
    Option StructDecl :=
  match env with
  | [] => none
  | (candidate, decl) :: rest =>
      if candidate == name then
        some decl
      else
        StructEnv.lookupName? rest name

def StructEnv.lookup? (env : StructEnv) (path : Path) :
    Option StructDecl := do
  let name ← pathLast? path
  StructEnv.lookupName? env name

def StructEnv.extendDecl (env : StructEnv) (decl : StructDecl) :
    StructEnv :=
  (decl.name, decl) :: env

def mapOption {α β : Type} (f : α -> Option β) : List α -> Option (List β)
  | [] => some []
  | item :: rest => do
      let head ← f item
      let tail ← mapOption f rest
      some (head :: tail)

def mapOptionIdx {α β : Type} (f : Nat -> α -> Option β) :
    Nat -> List α -> Option (List β)
  | _, [] => some []
  | index, item :: rest => do
      let head ← f index item
      let tail ← mapOptionIdx f (index + 1) rest
      some (head :: tail)

def mapIdx {α β : Type} (f : Nat -> α -> β) : Nat -> List α -> List β
  | _, [] => []
  | index, item :: rest =>
      f index item :: mapIdx f (index + 1) rest

def abiDecodeReturnExprs (tys : List CoreTy) (dataCore : CoreExpr) :
    List CoreExpr :=
  let decoded := SolidCore.Solidity.Source.Expr.abiDecode tys dataCore
  match tys with
  | [] => []
  | [_] => [decoded]
  | _ =>
      mapIdx
        (fun index _ =>
          SolidCore.Solidity.Source.Expr.index decoded
            (SolidCore.Solidity.Source.Expr.word index))
        0 tys

def filterMapOption {α β : Type} (f : α -> Option (Option β)) :
    List α -> Option (List β)
  | [] => some []
  | item :: rest => do
      let head? ← f item
      let tail ← filterMapOption f rest
      match head? with
      | some head => some (head :: tail)
      | none => some tail

def concatLists {α : Type} : List (List α) -> List α
  | [] => []
  | items :: rest => items ++ concatLists rest

def concatMapList {α β : Type} (f : α -> List β) :
    List α -> List β
  | [] => []
  | item :: rest => f item ++ concatMapList f rest

def listGet? {α : Type} : List α -> Nat -> Option α
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: rest, index + 1 => listGet? rest index

def appendUniqueContracts (contracts extra : List ContractDecl) :
    List ContractDecl :=
  extra.foldl
    (fun acc decl =>
      if nameIn decl.name (acc.map ContractDecl.name) then
        acc
      else
        acc ++ [decl])
    contracts

def defaultResolveUserTypesFuel : Nat := 1024

mutual

def Ty.resolveUserTypesFuel : Nat -> UserTypeEnv -> Ty -> Ty
  | 0, _, ty => ty
  | fuel + 1, env, ty =>
      let resolve := Ty.resolveUserTypesFuel fuel env
      match ty with
      | Ty.array element size => Ty.array (resolve element) size
      | Ty.mapping key value => Ty.mapping (resolve key) (resolve value)
      | Ty.tuple tys => Ty.tuple (tys.map resolve)
      | Ty.user path =>
          match UserTypeEnv.lookup? env path with
          | some underlying => resolve underlying
          | none => Ty.user path
      | Ty.function params returns mutability visibility =>
          Ty.function (params.map resolve) (returns.map resolve)
            mutability visibility
      | other => other

end

def Ty.resolveUserTypes (env : UserTypeEnv) (ty : Ty) : Ty :=
  Ty.resolveUserTypesFuel defaultResolveUserTypesFuel env ty

def Parameter.resolveUserTypes (env : UserTypeEnv)
    (param : Parameter) : Parameter :=
  { param with ty := Ty.resolveUserTypes env param.ty }

def VarBinding.resolveUserTypes (env : UserTypeEnv)
    (binding : VarBinding) : VarBinding :=
  { binding with ty := binding.ty.map (Ty.resolveUserTypes env) }

mutual

def Expr.resolveUserTypesFuel : Nat -> UserTypeEnv -> Expr -> Expr
  | 0, _, expr => expr
  | fuel + 1, env, expr =>
      let resolve := Expr.resolveUserTypesFuel fuel env
      let resolveArg := Arg.resolveUserTypesFuel fuel env
      let resolveOption := CallOption.resolveUserTypesFuel fuel env
      let resolveTupleItem := TupleItem.resolveUserTypesFuel fuel env
      match expr with
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName (Ty.resolveUserTypesFuel fuel env ty)
      | Expr.member (Expr.typeName ty@(Ty.user _)) member =>
          Expr.member (Expr.typeName ty) member
      | Expr.member base member => Expr.member (resolve base) member
      | Expr.index base index => Expr.index (resolve base) (resolve index)
      | Expr.slice base start stop =>
          Expr.slice (resolve base) (start.map resolve) (stop.map resolve)
      | Expr.call (Expr.typeName ty@(Ty.user _)) args =>
          Expr.call (Expr.typeName ty) (args.map resolveArg)
      | Expr.call (Expr.member (Expr.typeName ty@(Ty.user _)) member)
          [Arg.positional arg] =>
          if member == "wrap" || member == "unwrap" then
            Expr.call
              (Expr.typeName (Ty.resolveUserTypesFuel fuel env ty))
              [Arg.positional (resolve arg)]
          else
            Expr.call
              (Expr.member (Expr.typeName ty) member)
              [Arg.positional (resolve arg)]
      | Expr.call (Expr.member (Expr.typeName ty@(Ty.user _)) member) args =>
          Expr.call (Expr.member (Expr.typeName ty) member)
            (args.map resolveArg)
      | Expr.call fn args =>
          Expr.call (resolve fn) (args.map resolveArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (resolve fn)
            (options.map resolveOption) (args.map resolveArg)
      | Expr.newExpr ty args =>
          Expr.newExpr (Ty.resolveUserTypesFuel fuel env ty)
            (args.map resolveArg)
      | Expr.tuple items => Expr.tuple (items.map resolveTupleItem)
      | Expr.array exprs => Expr.array (exprs.map resolve)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (resolve inner)
      | Expr.unary op inner => Expr.unary op (resolve inner)
      | Expr.binary op lhs rhs => Expr.binary op (resolve lhs) (resolve rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (resolve cond) (resolve thenExpr) (resolve elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (resolve lhs) op (resolve rhs)
      | Expr.payableConversion inner => Expr.payableConversion (resolve inner)

def Arg.resolveUserTypesFuel : Nat -> UserTypeEnv -> Arg -> Arg
  | 0, _, arg => arg
  | fuel + 1, env, arg =>
      let resolve := Expr.resolveUserTypesFuel fuel env
      match arg with
      | Arg.positional expr => Arg.positional (resolve expr)
      | Arg.named name expr => Arg.named name (resolve expr)

def CallOption.resolveUserTypesFuel :
    Nat -> UserTypeEnv -> CallOption -> CallOption
  | 0, _, option => option
  | fuel + 1, env, option =>
      let resolve := Expr.resolveUserTypesFuel fuel env
      match option with
      | CallOption.named name expr => CallOption.named name (resolve expr)

def TupleItem.resolveUserTypesFuel :
    Nat -> UserTypeEnv -> TupleItem -> TupleItem
  | 0, _, item => item
  | fuel + 1, env, item =>
      let resolve := Expr.resolveUserTypesFuel fuel env
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (resolve expr)

end

def Expr.resolveUserTypes (env : UserTypeEnv) (expr : Expr) : Expr :=
  Expr.resolveUserTypesFuel defaultResolveUserTypesFuel env expr

def Arg.resolveUserTypes (env : UserTypeEnv) (arg : Arg) : Arg :=
  Arg.resolveUserTypesFuel defaultResolveUserTypesFuel env arg

def ModifierInvocation.resolveUserTypes (env : UserTypeEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with args := invocation.args.map (Arg.resolveUserTypes env) }

def StateVarDecl.resolveUserTypes (env : UserTypeEnv)
    (decl : StateVarDecl) : StateVarDecl :=
  { decl with
    ty := Ty.resolveUserTypes env decl.ty
    init := decl.init.map (Expr.resolveUserTypes env) }

def EventParam.resolveUserTypes (env : UserTypeEnv)
    (param : EventParam) : EventParam :=
  { param with ty := Ty.resolveUserTypes env param.ty }

def ErrorDecl.resolveUserTypes (env : UserTypeEnv)
    (decl : ErrorDecl) : ErrorDecl :=
  { decl with params := decl.params.map (Parameter.resolveUserTypes env) }

def StructField.resolveUserTypes (env : UserTypeEnv)
    (field : StructField) : StructField :=
  { field with ty := Ty.resolveUserTypes env field.ty }

def StructDecl.resolveUserTypes (env : UserTypeEnv)
    (decl : StructDecl) : StructDecl :=
  { decl with fields := decl.fields.map (StructField.resolveUserTypes env) }

def UserValueTypeDecl.resolveUserTypes (env : UserTypeEnv)
    (decl : UserValueTypeDecl) : UserValueTypeDecl :=
  { decl with underlying := Ty.resolveUserTypes env decl.underlying }

def UsingDecl.resolveUserTypes (env : UserTypeEnv)
    (decl : UsingDecl) : UsingDecl :=
  { decl with target := decl.target.map (Ty.resolveUserTypes env) }

mutual

def Stmt.resolveUserTypesFuel : Nat -> UserTypeEnv -> Stmt -> Stmt
  | 0, _, stmt => stmt
  | fuel + 1, env, stmt =>
      let resolveStmt := Stmt.resolveUserTypesFuel fuel env
      let resolveExpr := Expr.resolveUserTypesFuel fuel env
      let resolveClause := CatchClause.resolveUserTypesFuel fuel env
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body => Stmt.block (body.map resolveStmt)
      | Stmt.varDecl bindings init =>
          Stmt.varDecl (bindings.map (VarBinding.resolveUserTypes env))
            (init.map resolveExpr)
      | Stmt.expr expr => Stmt.expr (resolveExpr expr)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (resolveExpr cond) (resolveStmt thenBranch)
            (elseBranch.map resolveStmt)
      | Stmt.whileLoop cond body =>
          Stmt.whileLoop (resolveExpr cond) (resolveStmt body)
      | Stmt.doWhile body cond =>
          Stmt.doWhile (resolveStmt body) (resolveExpr cond)
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map resolveStmt) (cond.map resolveExpr)
            (post.map resolveExpr) (resolveStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch (resolveExpr expr) (clauses.map resolveClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          Stmt.tryCatchReturns (resolveExpr expr)
            (returns.map (Parameter.resolveUserTypes env))
            (resolveStmt success) (clauses.map resolveClause)
      | Stmt.emitEvent expr => Stmt.emitEvent (resolveExpr expr)
      | Stmt.revertCall expr => Stmt.revertCall (resolveExpr expr)
      | Stmt.returnValues expr? => Stmt.returnValues (expr?.map resolveExpr)
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (resolveStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.resolveUserTypesFuel :
    Nat -> UserTypeEnv -> CatchClause -> CatchClause
  | 0, _, clause => clause
  | fuel + 1, env, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name
            (params.map (Parameter.resolveUserTypes env))
            (Stmt.resolveUserTypesFuel fuel env body)

end

def Stmt.resolveUserTypes (env : UserTypeEnv) (stmt : Stmt) : Stmt :=
  Stmt.resolveUserTypesFuel defaultResolveUserTypesFuel env stmt

def FunctionDecl.resolveUserTypes (env : UserTypeEnv)
    (decl : FunctionDecl) : FunctionDecl :=
  { decl with
    params := decl.params.map (Parameter.resolveUserTypes env)
    returns := decl.returns.map (Parameter.resolveUserTypes env)
    modifiers := decl.modifiers.map (ModifierInvocation.resolveUserTypes env)
    body := decl.body.map (Stmt.resolveUserTypes env) }

def ModifierDecl.resolveUserTypes (env : UserTypeEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  { decl with
    params := decl.params.map (Parameter.resolveUserTypes env)
    body := decl.body.map (Stmt.resolveUserTypes env) }

def EventDecl.resolveUserTypes (env : UserTypeEnv)
    (decl : EventDecl) : EventDecl :=
  { decl with params := decl.params.map (EventParam.resolveUserTypes env) }

def ContractItem.resolveUserTypes (env : UserTypeEnv) :
    ContractItem -> ContractItem
  | ContractItem.stateVar decl =>
      ContractItem.stateVar (StateVarDecl.resolveUserTypes env decl)
  | ContractItem.function decl =>
      ContractItem.function (FunctionDecl.resolveUserTypes env decl)
  | ContractItem.modifierDecl decl =>
      ContractItem.modifierDecl (ModifierDecl.resolveUserTypes env decl)
  | ContractItem.eventDecl decl =>
      ContractItem.eventDecl (EventDecl.resolveUserTypes env decl)
  | ContractItem.errorDecl decl =>
      ContractItem.errorDecl (ErrorDecl.resolveUserTypes env decl)
  | ContractItem.structDecl decl =>
      ContractItem.structDecl (StructDecl.resolveUserTypes env decl)
  | ContractItem.enumDecl decl => ContractItem.enumDecl decl
  | ContractItem.userValueTypeDecl decl =>
      ContractItem.userValueTypeDecl
        (UserValueTypeDecl.resolveUserTypes env decl)
  | ContractItem.usingDecl decl =>
      ContractItem.usingDecl (UsingDecl.resolveUserTypes env decl)

def ContractDecl.resolveUserTypes (env : UserTypeEnv)
    (decl : ContractDecl) : ContractDecl :=
  { decl with
    bases :=
      decl.bases.map (fun spec =>
        { spec with args := spec.args.map (Expr.resolveUserTypes env) })
    items := decl.items.map (ContractItem.resolveUserTypes env) }

def SourceItem.resolveUserTypes (env : UserTypeEnv) :
    SourceItem -> SourceItem
  | SourceItem.pragma name version => SourceItem.pragma name version
  | SourceItem.importPath path alias? => SourceItem.importPath path alias?
  | SourceItem.contract decl =>
      SourceItem.contract (ContractDecl.resolveUserTypes env decl)
  | SourceItem.freeFunction decl =>
      SourceItem.freeFunction (FunctionDecl.resolveUserTypes env decl)
  | SourceItem.freeConstant decl =>
      SourceItem.freeConstant (StateVarDecl.resolveUserTypes env decl)
  | SourceItem.freeError decl =>
      SourceItem.freeError (ErrorDecl.resolveUserTypes env decl)
  | SourceItem.freeStruct decl =>
      SourceItem.freeStruct (StructDecl.resolveUserTypes env decl)
  | SourceItem.freeEnum decl => SourceItem.freeEnum decl
  | SourceItem.freeUserValueType decl =>
      SourceItem.freeUserValueType
        (UserValueTypeDecl.resolveUserTypes env decl)
  | SourceItem.usingDecl decl =>
      SourceItem.usingDecl (UsingDecl.resolveUserTypes env decl)

def EnumDecl.caseIndexFrom? (target : Name) :
    Nat -> List Name -> Option Nat
  | _, [] => none
  | index, candidate :: rest =>
      if candidate == target then
        some index
      else
        EnumDecl.caseIndexFrom? target (index + 1) rest

def EnumDecl.caseIndex? (decl : EnumDecl) (target : Name) :
    Option Nat :=
  EnumDecl.caseIndexFrom? target 0 decl.cases

def EnumDecl.maxValue? (decl : EnumDecl) : Option Nat :=
  match decl.cases with
  | [] => none
  | _ :: rest => some rest.length

def EnumDecl.toAbiSourceTy (_decl : EnumDecl) : Ty :=
  Ty.uint 8

def EnumDecl.toCoreSourceTy (_decl : EnumDecl) : Ty :=
  Ty.uint 256

mutual

def Ty.resolveEnumsFuel : Nat -> EnumEnv -> Ty -> Ty
  | 0, _, ty => ty
  | fuel + 1, env, ty =>
      let resolve := Ty.resolveEnumsFuel fuel env
      match ty with
      | Ty.array element size => Ty.array (resolve element) size
      | Ty.mapping key value => Ty.mapping (resolve key) (resolve value)
      | Ty.tuple tys => Ty.tuple (tys.map resolve)
      | Ty.user path =>
          match EnumEnv.lookup? env path with
          | some decl => EnumDecl.toAbiSourceTy decl
          | none => Ty.user path
      | Ty.function params returns mutability visibility =>
          Ty.function (params.map resolve) (returns.map resolve)
            mutability visibility
      | other => other

end

def Ty.resolveEnums (env : EnumEnv) (ty : Ty) : Ty :=
  Ty.resolveEnumsFuel defaultResolveUserTypesFuel env ty

def Parameter.resolveEnums (env : EnumEnv)
    (param : Parameter) : Parameter :=
  { param with ty := Ty.resolveEnums env param.ty }

def VarBinding.resolveEnums (env : EnumEnv)
    (binding : VarBinding) : VarBinding :=
  { binding with ty := binding.ty.map (Ty.resolveEnums env) }

mutual

def Expr.resolveEnumsFuel : Nat -> EnumEnv -> Expr -> Expr
  | 0, _, expr => expr
  | fuel + 1, env, expr =>
      let resolve := Expr.resolveEnumsFuel fuel env
      let resolveArg := Arg.resolveEnumsFuel fuel env
      let resolveOption := CallOption.resolveEnumsFuel fuel env
      let resolveTupleItem := TupleItem.resolveEnumsFuel fuel env
      match expr with
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName (Ty.resolveEnumsFuel fuel env ty)
      | Expr.member (Expr.typeName (Ty.user path)) member =>
          match EnumEnv.lookup? env path with
          | some decl =>
              if member == "min" then
                Expr.literal (Literal.number "0")
              else if member == "max" then
                match EnumDecl.maxValue? decl with
                | some maxValue =>
                    Expr.literal (Literal.number (toString maxValue))
                | none => Expr.member (Expr.typeName (Ty.user path)) member
              else
                match EnumDecl.caseIndex? decl member with
                | some index =>
                    Expr.literal (Literal.number (toString index))
                | none => Expr.member (Expr.typeName (Ty.user path)) member
          | none => Expr.member (Expr.typeName (Ty.user path)) member
      | Expr.member base member => Expr.member (resolve base) member
      | Expr.index base index => Expr.index (resolve base) (resolve index)
      | Expr.slice base start stop =>
          Expr.slice (resolve base) (start.map resolve) (stop.map resolve)
      | Expr.call (Expr.typeName (Ty.user path)) [Arg.positional arg] =>
          match EnumEnv.lookup? env path with
          | some decl =>
              match EnumDecl.maxValue? decl with
              | some maxValue =>
                  Expr.enumFromUInt maxValue (resolve arg)
              | none =>
                  Expr.call (Expr.typeName (Ty.user path))
                    [Arg.positional (resolve arg)]
          | none =>
              Expr.call (Expr.typeName (Ty.user path))
                [Arg.positional (resolve arg)]
      | Expr.call fn args =>
          Expr.call (resolve fn) (args.map resolveArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (resolve fn)
            (options.map resolveOption) (args.map resolveArg)
      | Expr.newExpr ty args =>
          Expr.newExpr (Ty.resolveEnumsFuel fuel env ty)
            (args.map resolveArg)
      | Expr.tuple items => Expr.tuple (items.map resolveTupleItem)
      | Expr.array exprs => Expr.array (exprs.map resolve)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (resolve inner)
      | Expr.unary op inner => Expr.unary op (resolve inner)
      | Expr.binary op lhs rhs => Expr.binary op (resolve lhs) (resolve rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (resolve cond) (resolve thenExpr) (resolve elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (resolve lhs) op (resolve rhs)
      | Expr.payableConversion inner => Expr.payableConversion (resolve inner)

def Arg.resolveEnumsFuel : Nat -> EnumEnv -> Arg -> Arg
  | 0, _, arg => arg
  | fuel + 1, env, arg =>
      let resolve := Expr.resolveEnumsFuel fuel env
      match arg with
      | Arg.positional expr => Arg.positional (resolve expr)
      | Arg.named name expr => Arg.named name (resolve expr)

def CallOption.resolveEnumsFuel :
    Nat -> EnumEnv -> CallOption -> CallOption
  | 0, _, option => option
  | fuel + 1, env, option =>
      let resolve := Expr.resolveEnumsFuel fuel env
      match option with
      | CallOption.named name expr => CallOption.named name (resolve expr)

def TupleItem.resolveEnumsFuel :
    Nat -> EnumEnv -> TupleItem -> TupleItem
  | 0, _, item => item
  | fuel + 1, env, item =>
      let resolve := Expr.resolveEnumsFuel fuel env
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (resolve expr)

end

def Expr.resolveEnums (env : EnumEnv) (expr : Expr) : Expr :=
  Expr.resolveEnumsFuel defaultResolveUserTypesFuel env expr

def Arg.resolveEnums (env : EnumEnv) (arg : Arg) : Arg :=
  Arg.resolveEnumsFuel defaultResolveUserTypesFuel env arg

def ModifierInvocation.resolveEnums (env : EnumEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with
    args :=
      invocation.args.map
        (fun arg =>
          Arg.resolveEnumsFuel defaultResolveUserTypesFuel env arg) }

def StateVarDecl.resolveEnums (env : EnumEnv)
    (decl : StateVarDecl) : StateVarDecl :=
  { decl with
    ty := Ty.resolveEnums env decl.ty
    init := decl.init.map (Expr.resolveEnums env) }

def EventParam.resolveEnums (env : EnumEnv)
    (param : EventParam) : EventParam :=
  { param with ty := Ty.resolveEnums env param.ty }

def ErrorDecl.resolveEnums (env : EnumEnv)
    (decl : ErrorDecl) : ErrorDecl :=
  { decl with params := decl.params.map (Parameter.resolveEnums env) }

def StructField.resolveEnums (env : EnumEnv)
    (field : StructField) : StructField :=
  { field with ty := Ty.resolveEnums env field.ty }

def StructDecl.resolveEnums (env : EnumEnv)
    (decl : StructDecl) : StructDecl :=
  { decl with fields := decl.fields.map (StructField.resolveEnums env) }

def UsingDecl.resolveEnums (env : EnumEnv)
    (decl : UsingDecl) : UsingDecl :=
  { decl with target := decl.target.map (Ty.resolveEnums env) }

mutual

def Stmt.resolveEnumsFuel : Nat -> EnumEnv -> Stmt -> Stmt
  | 0, _, stmt => stmt
  | fuel + 1, env, stmt =>
      let resolveStmt := Stmt.resolveEnumsFuel fuel env
      let resolveExpr := Expr.resolveEnumsFuel fuel env
      let resolveClause := CatchClause.resolveEnumsFuel fuel env
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body => Stmt.block (body.map resolveStmt)
      | Stmt.varDecl bindings init =>
          Stmt.varDecl (bindings.map (VarBinding.resolveEnums env))
            (init.map resolveExpr)
      | Stmt.expr expr => Stmt.expr (resolveExpr expr)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (resolveExpr cond) (resolveStmt thenBranch)
            (elseBranch.map resolveStmt)
      | Stmt.whileLoop cond body =>
          Stmt.whileLoop (resolveExpr cond) (resolveStmt body)
      | Stmt.doWhile body cond =>
          Stmt.doWhile (resolveStmt body) (resolveExpr cond)
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map resolveStmt) (cond.map resolveExpr)
            (post.map resolveExpr) (resolveStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch (resolveExpr expr) (clauses.map resolveClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          Stmt.tryCatchReturns (resolveExpr expr)
            (returns.map (Parameter.resolveEnums env))
            (resolveStmt success) (clauses.map resolveClause)
      | Stmt.emitEvent expr => Stmt.emitEvent (resolveExpr expr)
      | Stmt.revertCall expr => Stmt.revertCall (resolveExpr expr)
      | Stmt.returnValues expr? => Stmt.returnValues (expr?.map resolveExpr)
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (resolveStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.resolveEnumsFuel :
    Nat -> EnumEnv -> CatchClause -> CatchClause
  | 0, _, clause => clause
  | fuel + 1, env, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name
            (params.map (Parameter.resolveEnums env))
            (Stmt.resolveEnumsFuel fuel env body)

end

def Stmt.resolveEnums (env : EnumEnv) (stmt : Stmt) : Stmt :=
  Stmt.resolveEnumsFuel defaultResolveUserTypesFuel env stmt

def FunctionDecl.resolveEnums (env : EnumEnv)
    (decl : FunctionDecl) : FunctionDecl :=
  { decl with
    params := decl.params.map (Parameter.resolveEnums env)
    returns := decl.returns.map (Parameter.resolveEnums env)
    modifiers := decl.modifiers.map (ModifierInvocation.resolveEnums env)
    body := decl.body.map (Stmt.resolveEnums env) }

def ModifierDecl.resolveEnums (env : EnumEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  { decl with
    params := decl.params.map (Parameter.resolveEnums env)
    body := decl.body.map (Stmt.resolveEnums env) }

def EventDecl.resolveEnums (env : EnumEnv)
    (decl : EventDecl) : EventDecl :=
  { decl with params := decl.params.map (EventParam.resolveEnums env) }

def ContractItem.resolveEnums (env : EnumEnv) :
    ContractItem -> ContractItem
  | ContractItem.stateVar decl =>
      ContractItem.stateVar (StateVarDecl.resolveEnums env decl)
  | ContractItem.function decl =>
      ContractItem.function (FunctionDecl.resolveEnums env decl)
  | ContractItem.modifierDecl decl =>
      ContractItem.modifierDecl (ModifierDecl.resolveEnums env decl)
  | ContractItem.eventDecl decl =>
      ContractItem.eventDecl (EventDecl.resolveEnums env decl)
  | ContractItem.errorDecl decl =>
      ContractItem.errorDecl (ErrorDecl.resolveEnums env decl)
  | ContractItem.structDecl decl =>
      ContractItem.structDecl (StructDecl.resolveEnums env decl)
  | ContractItem.enumDecl decl => ContractItem.enumDecl decl
  | ContractItem.userValueTypeDecl decl =>
      ContractItem.userValueTypeDecl decl
  | ContractItem.usingDecl decl =>
      ContractItem.usingDecl (UsingDecl.resolveEnums env decl)

def ContractDecl.resolveEnums (env : EnumEnv)
    (decl : ContractDecl) : ContractDecl :=
  { decl with
    bases :=
      decl.bases.map (fun spec =>
        { spec with args := spec.args.map (Expr.resolveEnums env) })
    items := decl.items.map (ContractItem.resolveEnums env) }

def SourceItem.resolveEnums (env : EnumEnv) :
    SourceItem -> SourceItem
  | SourceItem.pragma name version => SourceItem.pragma name version
  | SourceItem.importPath path alias? => SourceItem.importPath path alias?
  | SourceItem.contract decl =>
      SourceItem.contract (ContractDecl.resolveEnums env decl)
  | SourceItem.freeFunction decl =>
      SourceItem.freeFunction (FunctionDecl.resolveEnums env decl)
  | SourceItem.freeConstant decl =>
      SourceItem.freeConstant (StateVarDecl.resolveEnums env decl)
  | SourceItem.freeError decl =>
      SourceItem.freeError (ErrorDecl.resolveEnums env decl)
  | SourceItem.freeStruct decl =>
      SourceItem.freeStruct (StructDecl.resolveEnums env decl)
  | SourceItem.freeEnum decl => SourceItem.freeEnum decl
  | SourceItem.freeUserValueType decl =>
      SourceItem.freeUserValueType decl
  | SourceItem.usingDecl decl =>
      SourceItem.usingDecl (UsingDecl.resolveEnums env decl)

def StructDecl.fieldIndexFrom? (target : Name) :
    Nat -> List StructField -> Option Nat
  | _, [] => none
  | index, field :: rest =>
      if field.name == target then
        some index
      else
        StructDecl.fieldIndexFrom? target (index + 1) rest

def StructDecl.fieldIndex? (decl : StructDecl) (target : Name) :
    Option Nat :=
  StructDecl.fieldIndexFrom? target 0 decl.fields

def StructDecl.field? (decl : StructDecl) (target : Name) :
    Option StructField :=
  decl.fields.find? (fun field => field.name == target)

def Ty.structDecl? (env : StructEnv) : Ty -> Option StructDecl
  | Ty.user path => StructEnv.lookup? env path
  | _ => none

mutual

def Ty.resolveStructsFuel : Nat -> StructEnv -> Ty -> Ty
  | 0, _, ty => ty
  | fuel + 1, env, ty =>
      let resolve := Ty.resolveStructsFuel fuel env
      match ty with
      | Ty.array element size => Ty.array (resolve element) size
      | Ty.mapping key value => Ty.mapping (resolve key) (resolve value)
      | Ty.tuple tys => Ty.tuple (tys.map resolve)
      | Ty.user path =>
          match StructEnv.lookup? env path with
          | some decl =>
              Ty.tuple (decl.fields.map (fun field => resolve field.ty))
          | none => Ty.user path
      | Ty.function params returns mutability visibility =>
          Ty.function (params.map resolve) (returns.map resolve)
            mutability visibility
      | other => other

end

def Ty.resolveStructs (env : StructEnv) (ty : Ty) : Ty :=
  Ty.resolveStructsFuel defaultResolveUserTypesFuel env ty

def StructDecl.toTupleTy (env : StructEnv) (decl : StructDecl) : Ty :=
  Ty.tuple (decl.fields.map (fun field => Ty.resolveStructs env field.ty))

def Parameter.resolveStructs (env : StructEnv)
    (param : Parameter) : Parameter :=
  { param with ty := Ty.resolveStructs env param.ty }

def VarBinding.resolveStructs (env : StructEnv)
    (binding : VarBinding) : VarBinding :=
  { binding with ty := binding.ty.map (Ty.resolveStructs env) }

def Parameter.extendStructTypeEnv (fallbackPrefix : String) (index : Nat)
    (env : TypeEnv) (param : Parameter) : TypeEnv :=
  TypeEnv.extend? env
    (some (param.name.getD (fallbackPrefix ++ toString index)))
    (some param.ty)

def Parameters.extendStructTypeEnvFrom (fallbackPrefix : String) :
    Nat -> TypeEnv -> List Parameter -> TypeEnv
  | _, env, [] => env
  | index, env, param :: rest =>
      Parameters.extendStructTypeEnvFrom fallbackPrefix (index + 1)
        (Parameter.extendStructTypeEnv fallbackPrefix index env param) rest

def Parameters.extendStructTypeEnv (fallbackPrefix : String)
    (env : TypeEnv) (params : List Parameter) : TypeEnv :=
  Parameters.extendStructTypeEnvFrom fallbackPrefix 0 env params

def VarBinding.extendStructTypeEnv (env : TypeEnv)
    (binding : VarBinding) : TypeEnv :=
  TypeEnv.extend? env binding.name binding.ty

def VarBindings.extendStructTypeEnv (env : TypeEnv) :
    List VarBinding -> TypeEnv
  | [] => env
  | binding :: rest =>
      VarBindings.extendStructTypeEnv
        (VarBinding.extendStructTypeEnv env binding) rest

def Arg.positionalExpr? : Arg -> Option Expr
  | Arg.positional expr => some expr
  | _ => none

def Args.toPositionalStructExprs? : List Arg -> Option (List Expr)
  | [] => some []
  | arg :: rest => do
      let head ← Arg.positionalExpr? arg
      let tail ← Args.toPositionalStructExprs? rest
      some (head :: tail)

def Args.findNamed? (name : Name) : List Arg -> Option Expr
  | [] => none
  | Arg.named candidate expr :: rest =>
      if candidate == name then
        some expr
      else
        Args.findNamed? name rest
  | _ :: rest => Args.findNamed? name rest

def StructDecl.constructorArgs? (decl : StructDecl)
    (args : List Arg) : Option (List Expr) :=
  if args.length == decl.fields.length then
    match args with
    | [] => some []
    | Arg.positional _ :: _ => Args.toPositionalStructExprs? args
    | Arg.named _ _ :: _ =>
        mapOption (fun field => Args.findNamed? field.name args) decl.fields
  else
    none

def Expr.structDeclWithEnv? (env : StructEnv) (typeEnv : TypeEnv) :
    Expr -> Option StructDecl
  | Expr.ident name => do
      let ty ← TypeEnv.lookup? typeEnv name
      Ty.structDecl? env ty
  | Expr.call (Expr.typeName (Ty.user path)) _ =>
      StructEnv.lookup? env path
  | Expr.member base member => do
      let baseDecl ← Expr.structDeclWithEnv? env typeEnv base
      let field ← StructDecl.field? baseDecl member
      Ty.structDecl? env field.ty
  | Expr.ternary _ thenExpr _ =>
      Expr.structDeclWithEnv? env typeEnv thenExpr
  | _ => none

mutual

def Expr.resolveStructsFuel :
    Nat -> StructEnv -> TypeEnv -> Expr -> Expr
  | 0, _, _, expr => expr
  | fuel + 1, env, typeEnv, expr =>
      let resolve := Expr.resolveStructsFuel fuel env typeEnv
      let resolveArg := Arg.resolveStructsFuel fuel env typeEnv
      let resolveOption := CallOption.resolveStructsFuel fuel env typeEnv
      let resolveTupleItem := TupleItem.resolveStructsFuel fuel env typeEnv
      match expr with
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName (Ty.resolveStructsFuel fuel env ty)
      | Expr.member base member =>
          match Expr.structDeclWithEnv? env typeEnv base with
          | some decl =>
              match StructDecl.fieldIndex? decl member with
              | some index =>
                  Expr.index (resolve base)
                    (Expr.literal (Literal.number (toString index)))
              | none => Expr.member (resolve base) member
          | none => Expr.member (resolve base) member
      | Expr.index base index => Expr.index (resolve base) (resolve index)
      | Expr.slice base start stop =>
          Expr.slice (resolve base) (start.map resolve) (stop.map resolve)
      | Expr.call (Expr.typeName (Ty.user path)) args =>
          match StructEnv.lookup? env path with
          | some decl =>
              match StructDecl.constructorArgs? decl args with
              | some fieldExprs =>
                  let typedArgs :=
                    (decl.fields.zip fieldExprs).map
                      (fun pair =>
                        Arg.positional
                          (Expr.call
                            (Expr.typeName
                              (Ty.resolveStructsFuel fuel env pair.fst.ty))
                            [Arg.positional (resolve pair.snd)]))
                  Expr.call
                    (Expr.member (Expr.ident "abi") "decode")
                    [ Arg.positional
                        (Expr.call
                          (Expr.member (Expr.ident "abi") "encode")
                          typedArgs)
                    , Arg.positional
                        (Expr.typeName
                          (Ty.tuple
                            (decl.fields.map
                              (fun field =>
                                Ty.resolveStructsFuel fuel env field.ty)))) ]
              | none =>
                  Expr.call (Expr.typeName (Ty.user path))
                    (args.map resolveArg)
          | none =>
              Expr.call
                (Expr.typeName (Ty.resolveStructsFuel fuel env (Ty.user path)))
                (args.map resolveArg)
      | Expr.call fn args =>
          Expr.call (resolve fn) (args.map resolveArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (resolve fn)
            (options.map resolveOption) (args.map resolveArg)
      | Expr.newExpr ty args =>
          Expr.newExpr (Ty.resolveStructsFuel fuel env ty)
            (args.map resolveArg)
      | Expr.tuple items => Expr.tuple (items.map resolveTupleItem)
      | Expr.array exprs => Expr.array (exprs.map resolve)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (resolve inner)
      | Expr.unary op inner => Expr.unary op (resolve inner)
      | Expr.binary op lhs rhs => Expr.binary op (resolve lhs) (resolve rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (resolve cond) (resolve thenExpr) (resolve elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (resolve lhs) op (resolve rhs)
      | Expr.payableConversion inner => Expr.payableConversion (resolve inner)

def Arg.resolveStructsFuel :
    Nat -> StructEnv -> TypeEnv -> Arg -> Arg
  | 0, _, _, arg => arg
  | fuel + 1, env, typeEnv, arg =>
      let resolve := Expr.resolveStructsFuel fuel env typeEnv
      match arg with
      | Arg.positional expr => Arg.positional (resolve expr)
      | Arg.named name expr => Arg.named name (resolve expr)

def CallOption.resolveStructsFuel :
    Nat -> StructEnv -> TypeEnv -> CallOption -> CallOption
  | 0, _, _, option => option
  | fuel + 1, env, typeEnv, option =>
      let resolve := Expr.resolveStructsFuel fuel env typeEnv
      match option with
      | CallOption.named name expr => CallOption.named name (resolve expr)

def TupleItem.resolveStructsFuel :
    Nat -> StructEnv -> TypeEnv -> TupleItem -> TupleItem
  | 0, _, _, item => item
  | fuel + 1, env, typeEnv, item =>
      let resolve := Expr.resolveStructsFuel fuel env typeEnv
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (resolve expr)

end

def Expr.resolveStructs (env : StructEnv) (typeEnv : TypeEnv)
    (expr : Expr) : Expr :=
  Expr.resolveStructsFuel defaultResolveUserTypesFuel env typeEnv expr

def Arg.resolveStructs (env : StructEnv) (typeEnv : TypeEnv)
    (arg : Arg) : Arg :=
  Arg.resolveStructsFuel defaultResolveUserTypesFuel env typeEnv arg

def ModifierInvocation.resolveStructs (env : StructEnv) (typeEnv : TypeEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with
    args :=
      invocation.args.map
        (fun arg =>
          Arg.resolveStructsFuel defaultResolveUserTypesFuel env typeEnv arg) }

def StateVarDecl.resolveStructs (env : StructEnv)
    (decl : StateVarDecl) : StateVarDecl :=
  { decl with
    ty := Ty.resolveStructs env decl.ty
    init := decl.init.map (Expr.resolveStructs env []) }

def EventParam.resolveStructs (env : StructEnv)
    (param : EventParam) : EventParam :=
  { param with ty := Ty.resolveStructs env param.ty }

def ErrorDecl.resolveStructs (env : StructEnv)
    (decl : ErrorDecl) : ErrorDecl :=
  { decl with params := decl.params.map (Parameter.resolveStructs env) }

def StructField.resolveStructs (env : StructEnv)
    (field : StructField) : StructField :=
  { field with ty := Ty.resolveStructs env field.ty }

def StructDecl.resolveStructs (env : StructEnv)
    (decl : StructDecl) : StructDecl :=
  { decl with fields := decl.fields.map (StructField.resolveStructs env) }

def UsingDecl.resolveStructs (env : StructEnv)
    (decl : UsingDecl) : UsingDecl :=
  { decl with target := decl.target.map (Ty.resolveStructs env) }

def Parameter.extendTypeEnv (fallbackPrefix : String) (index : Nat)
    (env : TypeEnv) (param : Parameter) : TypeEnv :=
  TypeEnv.extend? env
    (some (param.name.getD (fallbackPrefix ++ toString index)))
    (some param.ty)

def Parameters.extendTypeEnvFrom (fallbackPrefix : String) :
    Nat -> TypeEnv -> List Parameter -> TypeEnv
  | _, env, [] => env
  | index, env, param :: rest =>
      Parameters.extendTypeEnvFrom fallbackPrefix (index + 1)
        (Parameter.extendTypeEnv fallbackPrefix index env param) rest

def Parameters.extendTypeEnv (fallbackPrefix : String)
    (env : TypeEnv) (params : List Parameter) : TypeEnv :=
  Parameters.extendTypeEnvFrom fallbackPrefix 0 env params

def VarBinding.extendTypeEnv (env : TypeEnv) (binding : VarBinding) :
    TypeEnv :=
  TypeEnv.extend? env binding.name binding.ty

def VarBindings.extendTypeEnv (env : TypeEnv) :
    List VarBinding -> TypeEnv
  | [] => env
  | binding :: rest =>
      VarBindings.extendTypeEnv (VarBinding.extendTypeEnv env binding) rest

abbrev StorageRefEnv := List (Name × Bool)

def StorageRefEnv.lookup? (env : StorageRefEnv) (name : Name) :
    Option Bool :=
  match env with
  | [] => none
  | (candidate, isStorageRef) :: rest =>
      if candidate == name then
        some isStorageRef
      else
        StorageRefEnv.lookup? rest name

def StorageRefEnv.isStorageRef (env : StorageRefEnv) (name : Name) :
    Bool :=
  match StorageRefEnv.lookup? env name with
  | some true => true
  | _ => false

def VarBinding.extendStorageRefEnv (env : StorageRefEnv)
    (binding : VarBinding) : StorageRefEnv :=
  match binding.name with
  | some name =>
      let isStorageRef :=
        match binding.location with
        | some DataLocation.storage => true
        | _ => false
      (name, isStorageRef) :: env
  | none => env

def VarBindings.extendStorageRefEnv (env : StorageRefEnv) :
    List VarBinding -> StorageRefEnv
  | [] => env
  | binding :: rest =>
      VarBindings.extendStorageRefEnv
        (VarBinding.extendStorageRefEnv env binding) rest

def Parameter.extendStorageRefEnv (fallbackPrefix : String) (index : Nat)
    (env : StorageRefEnv) (param : Parameter) : StorageRefEnv :=
  let name := param.name.getD (fallbackPrefix ++ toString index)
  let isStorageRef :=
    match param.location with
    | some DataLocation.storage => true
    | _ => false
  (name, isStorageRef) :: env

def Parameters.extendStorageRefEnvFrom (fallbackPrefix : String) :
    Nat -> StorageRefEnv -> List Parameter -> StorageRefEnv
  | _, env, [] => env
  | index, env, param :: rest =>
      Parameters.extendStorageRefEnvFrom fallbackPrefix (index + 1)
        (Parameter.extendStorageRefEnv fallbackPrefix index env param) rest

def Parameters.extendStorageRefEnv (fallbackPrefix : String)
    (env : StorageRefEnv) (params : List Parameter) : StorageRefEnv :=
  Parameters.extendStorageRefEnvFrom fallbackPrefix 0 env params

def FunctionDecl.typeEnv (extra : TypeEnv) (decl : FunctionDecl) :
    TypeEnv :=
  let withParams := Parameters.extendTypeEnv "_arg" extra decl.params
  Parameters.extendTypeEnv "_ret" withParams decl.returns

mutual

def Stmt.resolveStructsInSeqFuel :
    Nat -> StructEnv -> TypeEnv -> Stmt -> Stmt × TypeEnv
  | 0, _, typeEnv, stmt => (stmt, typeEnv)
  | fuel + 1, env, typeEnv, stmt =>
      let resolveExpr := Expr.resolveStructsFuel fuel env typeEnv
      let resolveStmt (child : Stmt) :=
        (Stmt.resolveStructsInSeqFuel fuel env typeEnv child).fst
      let resolveSeq (seqEnv : TypeEnv) (body : List Stmt) :
          List Stmt × TypeEnv :=
        let step (acc : List Stmt × TypeEnv) (head : Stmt) :
            List Stmt × TypeEnv :=
          let (done, seqEnv) := acc
          let (head', seqEnv') :=
            Stmt.resolveStructsInSeqFuel fuel env seqEnv head
          (head' :: done, seqEnv')
        let (revBody, finalEnv) :=
          body.foldl step (([] : List Stmt), seqEnv)
        (revBody.reverse, finalEnv)
      let resolveClause : CatchClause -> CatchClause
        | CatchClause.clause name params body =>
            let clauseEnv := Parameters.extendTypeEnv "_catch" typeEnv params
            CatchClause.clause name
              (params.map (Parameter.resolveStructs env))
              ((Stmt.resolveStructsInSeqFuel fuel env clauseEnv body).fst)
      match stmt with
      | Stmt.empty => (Stmt.empty, typeEnv)
      | Stmt.block body =>
          let (body', _) := resolveSeq typeEnv body
          (Stmt.block body', typeEnv)
      | Stmt.varDecl bindings init =>
          let init' := init.map resolveExpr
          let typeEnv' := VarBindings.extendTypeEnv typeEnv bindings
          (Stmt.varDecl (bindings.map (VarBinding.resolveStructs env)) init',
            typeEnv')
      | Stmt.expr expr => (Stmt.expr (resolveExpr expr), typeEnv)
      | Stmt.ifElse cond thenBranch elseBranch =>
          (Stmt.ifElse (resolveExpr cond) (resolveStmt thenBranch)
            (elseBranch.map resolveStmt), typeEnv)
      | Stmt.whileLoop cond body =>
          (Stmt.whileLoop (resolveExpr cond) (resolveStmt body), typeEnv)
      | Stmt.doWhile body cond =>
          (Stmt.doWhile (resolveStmt body) (resolveExpr cond), typeEnv)
      | Stmt.forLoop init cond post body =>
          let (init', loopEnv) :=
            match init with
            | some initStmt =>
                let (stmt', env') :=
                  Stmt.resolveStructsInSeqFuel fuel env typeEnv initStmt
                (some stmt', env')
            | none => (none, typeEnv)
          let resolveLoopExpr := Expr.resolveStructsFuel fuel env loopEnv
          let body' := (Stmt.resolveStructsInSeqFuel fuel env loopEnv body).fst
          (Stmt.forLoop init' (cond.map resolveLoopExpr)
            (post.map resolveLoopExpr) body', typeEnv)
      | Stmt.tryCatch expr clauses =>
          (Stmt.tryCatch (resolveExpr expr) (clauses.map resolveClause),
            typeEnv)
      | Stmt.tryCatchReturns expr returns success clauses =>
          let successEnv := Parameters.extendTypeEnv "_try" typeEnv returns
          let success' :=
            (Stmt.resolveStructsInSeqFuel fuel env successEnv success).fst
          (Stmt.tryCatchReturns (resolveExpr expr)
            (returns.map (Parameter.resolveStructs env))
            success' (clauses.map resolveClause), typeEnv)
      | Stmt.emitEvent expr => (Stmt.emitEvent (resolveExpr expr), typeEnv)
      | Stmt.revertCall expr => (Stmt.revertCall (resolveExpr expr), typeEnv)
      | Stmt.returnValues expr? =>
          (Stmt.returnValues (expr?.map resolveExpr), typeEnv)
      | Stmt.break => (Stmt.break, typeEnv)
      | Stmt.continue => (Stmt.continue, typeEnv)
      | Stmt.unchecked body => (Stmt.unchecked (resolveStmt body), typeEnv)
      | Stmt.inlineAssembly code => (Stmt.inlineAssembly code, typeEnv)
      | Stmt.modifierPlaceholder => (Stmt.modifierPlaceholder, typeEnv)

end

def Stmt.resolveStructs (env : StructEnv) (typeEnv : TypeEnv)
    (stmt : Stmt) : Stmt :=
  (Stmt.resolveStructsInSeqFuel defaultResolveUserTypesFuel env typeEnv stmt).fst

def FunctionDecl.resolveStructsWithTypeEnv (env : StructEnv)
    (extra : TypeEnv) (decl : FunctionDecl) : FunctionDecl :=
  let typeEnv := FunctionDecl.typeEnv extra decl
  { decl with
    params := decl.params.map (Parameter.resolveStructs env)
    returns := decl.returns.map (Parameter.resolveStructs env)
    modifiers := decl.modifiers.map (ModifierInvocation.resolveStructs env typeEnv)
    body := decl.body.map (Stmt.resolveStructs env typeEnv) }

def FunctionDecl.resolveStructs (env : StructEnv)
    (decl : FunctionDecl) : FunctionDecl :=
  FunctionDecl.resolveStructsWithTypeEnv env [] decl

def ModifierDecl.resolveStructsWithTypeEnv (env : StructEnv)
    (extra : TypeEnv) (decl : ModifierDecl) : ModifierDecl :=
  let typeEnv := Parameters.extendTypeEnv "_arg" extra decl.params
  { decl with
    params := decl.params.map (Parameter.resolveStructs env)
    body := decl.body.map (Stmt.resolveStructs env typeEnv) }

def ModifierDecl.resolveStructs (env : StructEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  ModifierDecl.resolveStructsWithTypeEnv env [] decl

def EventDecl.resolveStructs (env : StructEnv)
    (decl : EventDecl) : EventDecl :=
  { decl with params := decl.params.map (EventParam.resolveStructs env) }

def ContractItem.resolveStructsWithTypeEnv (env : StructEnv)
    (typeEnv : TypeEnv) :
    ContractItem -> ContractItem
  | ContractItem.stateVar decl =>
      ContractItem.stateVar (StateVarDecl.resolveStructs env decl)
  | ContractItem.function decl =>
      ContractItem.function
        (FunctionDecl.resolveStructsWithTypeEnv env typeEnv decl)
  | ContractItem.modifierDecl decl =>
      ContractItem.modifierDecl
        (ModifierDecl.resolveStructsWithTypeEnv env typeEnv decl)
  | ContractItem.eventDecl decl =>
      ContractItem.eventDecl (EventDecl.resolveStructs env decl)
  | ContractItem.errorDecl decl =>
      ContractItem.errorDecl (ErrorDecl.resolveStructs env decl)
  | ContractItem.structDecl decl =>
      ContractItem.structDecl (StructDecl.resolveStructs env decl)
  | ContractItem.enumDecl decl => ContractItem.enumDecl decl
  | ContractItem.userValueTypeDecl decl =>
      ContractItem.userValueTypeDecl decl
  | ContractItem.usingDecl decl =>
      ContractItem.usingDecl (UsingDecl.resolveStructs env decl)

def ContractItem.resolveStructs (env : StructEnv) :
    ContractItem -> ContractItem :=
  ContractItem.resolveStructsWithTypeEnv env []

def StateVarDecl.extendTypeEnv (typeEnv : TypeEnv)
    (decl : StateVarDecl) : TypeEnv :=
  TypeEnv.extend? typeEnv (some decl.name) (some decl.ty)

def StateVars.extendTypeEnv (typeEnv : TypeEnv) :
    List StateVarDecl -> TypeEnv
  | [] => typeEnv
  | decl :: rest =>
      StateVars.extendTypeEnv
        (StateVarDecl.extendTypeEnv typeEnv decl) rest

def ContractDecl.resolveStructs (env : StructEnv)
    (decl : ContractDecl) : ContractDecl :=
  let stateVars :=
    decl.items.filterMap (fun item =>
      match item with
      | ContractItem.stateVar stateVar => some stateVar
      | _ => none)
  let typeEnv := StateVars.extendTypeEnv [] stateVars
  { decl with
    bases :=
      decl.bases.map (fun spec =>
        { spec with args := spec.args.map (Expr.resolveStructs env []) })
    items := decl.items.map (ContractItem.resolveStructsWithTypeEnv env typeEnv) }

def SourceItem.resolveStructs (env : StructEnv) :
    SourceItem -> SourceItem
  | SourceItem.pragma name version => SourceItem.pragma name version
  | SourceItem.importPath path alias? => SourceItem.importPath path alias?
  | SourceItem.contract decl =>
      SourceItem.contract (ContractDecl.resolveStructs env decl)
  | SourceItem.freeFunction decl =>
      SourceItem.freeFunction (FunctionDecl.resolveStructs env decl)
  | SourceItem.freeConstant decl =>
      SourceItem.freeConstant (StateVarDecl.resolveStructs env decl)
  | SourceItem.freeError decl =>
      SourceItem.freeError (ErrorDecl.resolveStructs env decl)
  | SourceItem.freeStruct decl =>
      SourceItem.freeStruct (StructDecl.resolveStructs env decl)
  | SourceItem.freeEnum decl => SourceItem.freeEnum decl
  | SourceItem.freeUserValueType decl =>
      SourceItem.freeUserValueType decl
  | SourceItem.usingDecl decl =>
      SourceItem.usingDecl (UsingDecl.resolveStructs env decl)

def ContractDecl.findImmediateDerivedInOrder?
    (storageOrder : List ContractDecl) (decl : ContractDecl) :
    Option ContractDecl :=
  match storageOrder with
  | [] => none
  | [_] => none
  | current :: next :: rest =>
      if current.name == decl.name then
        some next
      else
        ContractDecl.findImmediateDerivedInOrder? (next :: rest) decl

def ContractDecl.baseSpecifierFor? (derived base : ContractDecl) :
    Option BaseSpecifier :=
  derived.bases.find? (fun spec =>
    match pathLast? spec.base with
    | some name => name == base.name
    | none => false)

mutual

def Ty.toCore? : Ty -> Option CoreTy
  | Ty.bool => some SolidCore.Solidity.Source.Ty.bool
  | Ty.address _ => some SolidCore.Solidity.Source.Ty.address
  | Ty.uint bits =>
      if bits == 0 || (bits % 8 == 0 && bits <= 256) then
        some SolidCore.Solidity.Source.Ty.uint256
      else
        none
  | Ty.int bits =>
      if bits == 0 || (bits % 8 == 0 && bits <= 256) then
        some SolidCore.Solidity.Source.Ty.int256
      else
        none
  | Ty.bytesN size =>
      if 0 < size && size <= 32 then
        some (SolidCore.Solidity.Source.Ty.fixedBytes size)
      else
        none
  | Ty.fixedBytes size =>
      if 0 < size && size <= 32 then
        some (SolidCore.Solidity.Source.Ty.fixedBytes size)
      else
        none
  | Ty.bytes => some SolidCore.Solidity.Source.Ty.bytesCalldata
  | Ty.string => some SolidCore.Solidity.Source.Ty.bytesCalldata
  | Ty.array ty none => do
      let element ← Ty.toCore? ty
      some (SolidCore.Solidity.Source.Ty.dynamicArray element)
  | Ty.array ty (some size) => do
      let element ← Ty.toCore? ty
      some (SolidCore.Solidity.Source.Ty.fixedArray size element)
  | Ty.tuple tys => do
      let coreTys ← Ty.listToCore? tys
      some (SolidCore.Solidity.Source.Ty.tuple coreTys)
  | Ty.user _ => some SolidCore.Solidity.Source.Ty.address
  | _ => none

def Ty.listToCore? : List Ty -> Option (List CoreTy)
  | [] => some []
  | ty :: rest => do
      let head ← Ty.toCore? ty
      let tail ← Ty.listToCore? rest
      some (head :: tail)

end

def Ty.toCoreStorageWord? : Ty -> Option CoreTy
  | Ty.bool => some SolidCore.Solidity.Source.Ty.bool
  | Ty.address _ => some SolidCore.Solidity.Source.Ty.address
  | Ty.uint bits =>
      if bits == 0 || (bits % 8 == 0 && bits <= 256) then
        some SolidCore.Solidity.Source.Ty.uint256
      else
        none
  | Ty.int bits =>
      if bits == 0 || (bits % 8 == 0 && bits <= 256) then
        some SolidCore.Solidity.Source.Ty.int256
      else
        none
  | Ty.bytesN size =>
      if 0 < size && size <= 32 then
        some (SolidCore.Solidity.Source.Ty.fixedBytes size)
      else
        none
  | Ty.fixedBytes size =>
      if 0 < size && size <= 32 then
        some (SolidCore.Solidity.Source.Ty.fixedBytes size)
      else
        none
  | _ => none

def Ty.toCoreMappingKey? : Ty -> Option CoreTy
  | Ty.bytes => some SolidCore.Solidity.Source.Ty.bytesCalldata
  | Ty.string => some SolidCore.Solidity.Source.Ty.bytesCalldata
  | ty => Ty.toCoreStorageWord? ty

def Ty.toCoreStorageLayout? : Ty -> Option CoreStorageLayout
  | Ty.bytes => some SolidCore.Solidity.Source.StorageLayout.bytes
  | Ty.string => some SolidCore.Solidity.Source.StorageLayout.string
  | Ty.tuple tys => do
      let fields ← mapOption Ty.toCoreStorageWord? tys
      some (SolidCore.Solidity.Source.StorageLayout.struct fields)
  | Ty.array elementTy none => do
      let element ← Ty.toCoreStorageWord? elementTy
      some (SolidCore.Solidity.Source.StorageLayout.dynamicArray element)
  | Ty.array elementTy (some size) => do
      let element ← Ty.toCoreStorageWord? elementTy
      some (SolidCore.Solidity.Source.StorageLayout.fixedArray size element)
  | Ty.mapping keyTy valueTy => do
      let key ← Ty.toCoreMappingKey? keyTy
      let value ← Ty.toCoreStorageWord? valueTy
      some (SolidCore.Solidity.Source.StorageLayout.mapping key value)
  | ty => do
      let scalar ← Ty.toCoreStorageWord? ty
      some (SolidCore.Solidity.Source.StorageLayout.scalar scalar)

def Ty.hasStorageArrayMembers : Ty -> Bool
  | Ty.array _ none => true
  | Ty.bytes => true
  | _ => false

def joinStringsWith (sep : String) : List String -> String
  | [] => ""
  | [item] => item
  | item :: rest => item ++ sep ++ joinStringsWith sep rest

mutual

def Ty.abiCanonical? : Ty -> Option String
  | Ty.bool => some "bool"
  | Ty.address _ => some "address"
  | Ty.uint bits =>
      if bits == 0 then
        some "uint256"
      else if bits % 8 == 0 && bits <= 256 then
        some ("uint" ++ toString bits)
      else
        none
  | Ty.int bits =>
      if bits == 0 then
        some "int256"
      else if bits % 8 == 0 && bits <= 256 then
        some ("int" ++ toString bits)
      else
        none
  | Ty.bytesN size =>
      if 0 < size && size <= 32 then
        some ("bytes" ++ toString size)
      else
        none
  | Ty.fixedBytes size =>
      if 0 < size && size <= 32 then
        some ("bytes" ++ toString size)
      else
        none
  | Ty.bytes => some "bytes"
  | Ty.string => some "string"
  | Ty.array ty none => do
      let base ← Ty.abiCanonical? ty
      some (base ++ "[]")
  | Ty.array ty (some size) => do
      let base ← Ty.abiCanonical? ty
      some (base ++ "[" ++ toString size ++ "]")
  | Ty.tuple tys => do
      let elements ← Ty.listAbiCanonical? tys
      some ("(" ++ joinStringsWith "," elements ++ ")")
  | Ty.user _ => some "address"
  | Ty.function _ _ _ _ => some "function"
  | _ => none

def Ty.listAbiCanonical? : List Ty -> Option (List String)
  | [] => some []
  | ty :: rest => do
      let head ← Ty.abiCanonical? ty
      let tail ← Ty.listAbiCanonical? rest
      some (head :: tail)

end

def UnaryOp.toCore? : UnaryOp -> Option SolidCore.Solidity.Source.UnaryOp
  | UnaryOp.logicalNot => some SolidCore.Solidity.Source.UnaryOp.logicalNot
  | UnaryOp.bitNot => some SolidCore.Solidity.Source.UnaryOp.bitNot
  | UnaryOp.neg => some SolidCore.Solidity.Source.UnaryOp.neg
  | _ => none

def BinaryOp.toCore? (op : BinaryOp) :
    Option SolidCore.Solidity.Source.BinaryOp :=
  some
    (match op with
    | BinaryOp.add => SolidCore.Solidity.Source.BinaryOp.add
    | BinaryOp.sub => SolidCore.Solidity.Source.BinaryOp.sub
    | BinaryOp.mul => SolidCore.Solidity.Source.BinaryOp.mul
    | BinaryOp.div => SolidCore.Solidity.Source.BinaryOp.div
    | BinaryOp.mod => SolidCore.Solidity.Source.BinaryOp.mod
    | BinaryOp.exp => SolidCore.Solidity.Source.BinaryOp.exp
    | BinaryOp.bitAnd => SolidCore.Solidity.Source.BinaryOp.bitAnd
    | BinaryOp.bitOr => SolidCore.Solidity.Source.BinaryOp.bitOr
    | BinaryOp.bitXor => SolidCore.Solidity.Source.BinaryOp.bitXor
    | BinaryOp.shl => SolidCore.Solidity.Source.BinaryOp.shl
    | BinaryOp.shr => SolidCore.Solidity.Source.BinaryOp.shr
    | BinaryOp.sar => SolidCore.Solidity.Source.BinaryOp.sar
    | BinaryOp.lt => SolidCore.Solidity.Source.BinaryOp.lt
    | BinaryOp.gt => SolidCore.Solidity.Source.BinaryOp.gt
    | BinaryOp.le => SolidCore.Solidity.Source.BinaryOp.le
    | BinaryOp.ge => SolidCore.Solidity.Source.BinaryOp.ge
    | BinaryOp.eq => SolidCore.Solidity.Source.BinaryOp.eq
    | BinaryOp.ne => SolidCore.Solidity.Source.BinaryOp.ne
    | BinaryOp.boolAnd => SolidCore.Solidity.Source.BinaryOp.boolAnd
    | BinaryOp.boolOr => SolidCore.Solidity.Source.BinaryOp.boolOr)

def AssignOp.toCoreBinary? : AssignOp -> Option SolidCore.Solidity.Source.BinaryOp
  | AssignOp.addAssign => some SolidCore.Solidity.Source.BinaryOp.add
  | AssignOp.subAssign => some SolidCore.Solidity.Source.BinaryOp.sub
  | AssignOp.mulAssign => some SolidCore.Solidity.Source.BinaryOp.mul
  | AssignOp.divAssign => some SolidCore.Solidity.Source.BinaryOp.div
  | AssignOp.modAssign => some SolidCore.Solidity.Source.BinaryOp.mod
  | AssignOp.bitAndAssign => some SolidCore.Solidity.Source.BinaryOp.bitAnd
  | AssignOp.bitOrAssign => some SolidCore.Solidity.Source.BinaryOp.bitOr
  | AssignOp.bitXorAssign => some SolidCore.Solidity.Source.BinaryOp.bitXor
  | AssignOp.shlAssign => some SolidCore.Solidity.Source.BinaryOp.shl
  | AssignOp.shrAssign => some SolidCore.Solidity.Source.BinaryOp.shr
  | AssignOp.sarAssign => some SolidCore.Solidity.Source.BinaryOp.sar
  | _ => none

def decimalDigit? (ch : Char) : Option Nat :=
  let value := ch.toNat
  if '0'.toNat <= value && value <= '9'.toNat then
    some (value - '0'.toNat)
  else
    none

def parseSeparatedDigits? (digit? : Char -> Option Nat) :
    List Char -> Option (List Nat)
  | [] => none
  | ch :: rest => do
      let digit ← digit? ch
      let tail ← parseSeparatedDigitsAfter? digit? rest
      some (digit :: tail)
where
  parseSeparatedDigitsAfter? (digit? : Char -> Option Nat) :
      List Char -> Option (List Nat)
    | [] => some []
    | '_' :: ch :: rest => do
        let digit ← digit? ch
        let tail ← parseSeparatedDigitsAfter? digit? rest
        some (digit :: tail)
    | ch :: rest => do
        let digit ← digit? ch
        let tail ← parseSeparatedDigitsAfter? digit? rest
        some (digit :: tail)

def digitsToNat (base : Nat) : Nat -> List Nat -> Nat
  | acc, [] => acc
  | acc, digit :: rest => digitsToNat base (acc * base + digit) rest

def decimalDigitsNoLeadingZero? (digits : List Nat) : Option (List Nat) :=
  match digits with
  | 0 :: _ :: _ => none
  | _ => some digits

def parseDecimalIntegerDigits? (chars : List Char) : Option (List Nat) := do
  let digits ← parseSeparatedDigits? decimalDigit? chars
  decimalDigitsNoLeadingZero? digits

def charIn (needle : Char) : List Char -> Bool
  | [] => false
  | ch :: rest => ch == needle || charIn needle rest

def splitOnDecimalPoint? :
    List Char -> Option (List Char × Option (List Char))
  | [] => some ([], none)
  | '.' :: rest =>
      if charIn '.' rest then
        none
      else
        some ([], some rest)
  | ch :: rest => do
      let split ← splitOnDecimalPoint? rest
      match split with
      | (whole, fraction?) => some (ch :: whole, fraction?)

def parseDecimalMantissa? (chars : List Char) :
    Option (List Nat × Nat) := do
  let split ← splitOnDecimalPoint? chars
  match split with
  | (wholeChars, none) => do
      let digits ← parseDecimalIntegerDigits? wholeChars
      some (digits, 0)
  | (wholeChars, some fractionChars) => do
      let wholeDigits ←
        match wholeChars with
        | [] => some []
        | _ => parseDecimalIntegerDigits? wholeChars
      let fractionDigits ←
        parseSeparatedDigits? decimalDigit? fractionChars
      some (wholeDigits ++ fractionDigits, fractionDigits.length)

def parseDecimalExponentSuffix? :
    List Char -> Option (Bool × Nat)
  | '+' :: rest => do
      let digits ← parseSeparatedDigits? decimalDigit? rest
      some (false, digitsToNat 10 0 digits)
  | '-' :: rest => do
      let digits ← parseSeparatedDigits? decimalDigit? rest
      some (true, digitsToNat 10 0 digits)
  | chars => do
      let digits ← parseSeparatedDigits? decimalDigit? chars
      some (false, digitsToNat 10 0 digits)

def splitDecimalExponent? :
    List Char -> Option (List Char × Option (Bool × Nat))
  | [] => some ([], none)
  | 'e' :: rest => do
      let exponent ← parseDecimalExponentSuffix? rest
      some ([], some exponent)
  | 'E' :: rest => do
      let exponent ← parseDecimalExponentSuffix? rest
      some ([], some exponent)
  | ch :: rest => do
      let split ← splitDecimalExponent? rest
      match split with
      | (mantissa, exponent?) => some (ch :: mantissa, exponent?)

def divideIfExact? (value divisor : Nat) : Option Nat :=
  if divisor == 0 then
    none
  else if value % divisor == 0 then
    some (value / divisor)
  else
    none

structure NumberRat where
  num : Nat
  den : Nat
  deriving Repr

def NumberRat.ofNat (value : Nat) : NumberRat :=
  { num := value, den := 1 }

def NumberRat.mk? (num den : Nat) : Option NumberRat :=
  if den == 0 then
    none
  else
    some { num, den }

def NumberRat.exactNat? (value : NumberRat) : Option Nat :=
  divideIfExact? value.num value.den

def decimalValueWithScaleRat? (digits : List Nat) (fractionDigits : Nat)
    (exponent? : Option (Bool × Nat)) : Option NumberRat :=
  let value := digitsToNat 10 0 digits
  match exponent? with
  | none =>
      NumberRat.mk? value (10 ^ fractionDigits)
  | some (false, exponent) =>
      if fractionDigits <= exponent then
        some (NumberRat.ofNat (value * (10 ^ (exponent - fractionDigits))))
      else
        NumberRat.mk? value (10 ^ (fractionDigits - exponent))
  | some (true, exponent) =>
      NumberRat.mk? value (10 ^ (fractionDigits + exponent))

def parseDecimalRatChars? (chars : List Char) : Option NumberRat := do
  let split ← splitDecimalExponent? chars
  match split with
  | (mantissaChars, exponent?) => do
      let parsed ← parseDecimalMantissa? mantissaChars
      match parsed with
      | (digits, fractionDigits) =>
          decimalValueWithScaleRat? digits fractionDigits exponent?

def parseDecimalNatChars? (chars : List Char) : Option Nat := do
  let value ← parseDecimalRatChars? chars
  value.exactNat?

def parseDecimalNat? (text : String) : Option Nat :=
  parseDecimalNatChars? text.toList

def parseDecimalNat (text : String) : Nat :=
  (parseDecimalNat? text).getD 0

def hexDigit? (ch : Char) : Option Nat :=
  let value := ch.toNat
  if '0'.toNat <= value && value <= '9'.toNat then
    some (value - '0'.toNat)
  else if 'a'.toNat <= value && value <= 'f'.toNat then
    some (10 + value - 'a'.toNat)
  else if 'A'.toNat <= value && value <= 'F'.toNat then
    some (10 + value - 'A'.toNat)
  else
    none

def parseHexNatChars? (chars : List Char) : Option Nat := do
  let digits ← parseSeparatedDigits? hexDigit? chars
  some (digitsToNat 16 0 digits)

def parseNumberNat? (text : String) : Option Nat :=
  match text.toList with
  | '0' :: 'x' :: rest => parseHexNatChars? rest
  | '0' :: 'X' :: rest => parseHexNatChars? rest
  | chars => parseDecimalNatChars? chars

def parseNumberRat? (text : String) : Option NumberRat :=
  match text.toList with
  | '0' :: 'x' :: rest => do
      let value ← parseHexNatChars? rest
      some (NumberRat.ofNat value)
  | '0' :: 'X' :: rest => do
      let value ← parseHexNatChars? rest
      some (NumberRat.ofNat value)
  | chars => parseDecimalRatChars? chars

def NumberRat.add (lhs rhs : NumberRat) : NumberRat :=
  { num := lhs.num * rhs.den + rhs.num * lhs.den
    den := lhs.den * rhs.den }

def NumberRat.sub? (lhs rhs : NumberRat) : Option NumberRat :=
  let lhsNum := lhs.num * rhs.den
  let rhsNum := rhs.num * lhs.den
  if rhsNum <= lhsNum then
    NumberRat.mk? (lhsNum - rhsNum) (lhs.den * rhs.den)
  else
    none

def NumberRat.mul (lhs rhs : NumberRat) : NumberRat :=
  { num := lhs.num * rhs.num
    den := lhs.den * rhs.den }

def NumberRat.scaleNat (value : NumberRat) (factor : Nat) : NumberRat :=
  { value with num := value.num * factor }

def parseUnitNumberRat? (text : String)
    (unit : UnitDenomination) : Option NumberRat := do
  let value ← parseNumberRat? text
  some (value.scaleNat unit.factor)

def parseUnitNumberNat? (text : String)
    (unit : UnitDenomination) : Option Nat := do
  let value ← parseUnitNumberRat? text unit
  value.exactNat?

def NumberRat.div? (lhs rhs : NumberRat) : Option NumberRat :=
  if rhs.num == 0 then
    none
  else
    NumberRat.mk? (lhs.num * rhs.den) (lhs.den * rhs.num)

def NumberRat.mod? (lhs rhs : NumberRat) : Option NumberRat := do
  let lhsNat ← lhs.exactNat?
  let rhsNat ← rhs.exactNat?
  if rhsNat == 0 then
    none
  else
    some (NumberRat.ofNat (lhsNat % rhsNat))

def NumberRat.pow (base : NumberRat) (exponent : Nat) : NumberRat :=
  { num := base.num ^ exponent
    den := base.den ^ exponent }

def NumberRat.bitAnd? (lhs rhs : NumberRat) : Option NumberRat := do
  let lhsNat ← lhs.exactNat?
  let rhsNat ← rhs.exactNat?
  some (NumberRat.ofNat (Nat.land lhsNat rhsNat))

def NumberRat.bitOr? (lhs rhs : NumberRat) : Option NumberRat := do
  let lhsNat ← lhs.exactNat?
  let rhsNat ← rhs.exactNat?
  some (NumberRat.ofNat (Nat.lor lhsNat rhsNat))

def NumberRat.bitXor? (lhs rhs : NumberRat) : Option NumberRat := do
  let lhsNat ← lhs.exactNat?
  let rhsNat ← rhs.exactNat?
  some (NumberRat.ofNat (Nat.xor lhsNat rhsNat))

def NumberRat.shl? (lhs rhs : NumberRat) : Option NumberRat := do
  let lhsNat ← lhs.exactNat?
  let rhsNat ← rhs.exactNat?
  some (NumberRat.ofNat (lhsNat * 2 ^ rhsNat))

def NumberRat.shr? (lhs rhs : NumberRat) : Option NumberRat := do
  let lhsNat ← lhs.exactNat?
  let rhsNat ← rhs.exactNat?
  some (NumberRat.ofNat (lhsNat / 2 ^ rhsNat))

def NumberRat.compareNum (lhs rhs : NumberRat) : Nat × Nat :=
  (lhs.num * rhs.den, rhs.num * lhs.den)

def NumberRat.lt (lhs rhs : NumberRat) : Bool :=
  let pair := NumberRat.compareNum lhs rhs
  pair.fst < pair.snd

def NumberRat.eq (lhs rhs : NumberRat) : Bool :=
  let pair := NumberRat.compareNum lhs rhs
  pair.fst == pair.snd

def NumberRat.le (lhs rhs : NumberRat) : Bool :=
  NumberRat.lt lhs rhs || NumberRat.eq lhs rhs

def BinaryOp.applyNumberRat? (op : BinaryOp)
    (lhs rhs : NumberRat) : Option NumberRat :=
  match op with
  | BinaryOp.add => some (lhs.add rhs)
  | BinaryOp.sub => lhs.sub? rhs
  | BinaryOp.mul => some (lhs.mul rhs)
  | BinaryOp.div => lhs.div? rhs
  | BinaryOp.mod => lhs.mod? rhs
  | BinaryOp.exp => do
      let exponent ← rhs.exactNat?
      some (lhs.pow exponent)
  | BinaryOp.bitAnd => lhs.bitAnd? rhs
  | BinaryOp.bitOr => lhs.bitOr? rhs
  | BinaryOp.bitXor => lhs.bitXor? rhs
  | BinaryOp.shl => lhs.shl? rhs
  | BinaryOp.shr => lhs.shr? rhs
  | BinaryOp.sar => lhs.shr? rhs
  | _ => none

def BinaryOp.applyNumberBool? (op : BinaryOp)
    (lhs rhs : NumberRat) : Option Bool :=
  match op with
  | BinaryOp.lt => some (lhs.lt rhs)
  | BinaryOp.gt => some (rhs.lt lhs)
  | BinaryOp.le => some (lhs.le rhs)
  | BinaryOp.ge => some (rhs.le lhs)
  | BinaryOp.eq => some (lhs.eq rhs)
  | BinaryOp.ne => some (!(lhs.eq rhs))
  | _ => none

def numberLiteralBoolWord (value : Bool) : Word :=
  SolidCore.Solidity.Source.boolWord value

mutual

def Expr.numberLiteralRat? : Expr -> Option NumberRat
  | Expr.literal (Literal.number text) => parseNumberRat? text
  | Expr.literal (Literal.unitNumber text unit) =>
      parseUnitNumberRat? text unit
  | Expr.binary op lhs rhs => do
      let lhsValue ← Expr.numberLiteralRat? lhs
      let rhsValue ← Expr.numberLiteralRat? rhs
      BinaryOp.applyNumberRat? op lhsValue rhsValue
  | Expr.call (Expr.typeName _) [Arg.positional expr] =>
      Expr.numberLiteralRat? expr
  | _ => none

def Expr.numberLiteralBool? : Expr -> Option Bool
  | Expr.binary op lhs rhs => do
      let lhsValue ← Expr.numberLiteralRat? lhs
      let rhsValue ← Expr.numberLiteralRat? rhs
      BinaryOp.applyNumberBool? op lhsValue rhsValue
  | _ => none

end

def parseHexStringChars? : List Char -> Option (List Byte)
  | [] => some []
  | '_' :: rest => parseHexStringChars? rest
  | hi :: '_' :: rest => parseHexStringChars? (hi :: rest)
  | hi :: lo :: rest => do
      let high ← hexDigit? hi
      let low ← hexDigit? lo
      let tail ← parseHexStringChars? rest
      some ((high * 16 + low) :: tail)
  | [_] => none

def parseHexString? (text : String) : Option (List Byte) :=
  parseHexStringChars? text.toList

def Ty.fixedBytesSize? : Ty -> Option Nat
  | Ty.bytesN size =>
      if 0 < size && size <= 32 then
        some size
      else
        none
  | Ty.fixedBytes size =>
      if 0 < size && size <= 32 then
        some size
      else
        none
  | _ => none

def Ty.isFixedBytes (ty : Ty) : Bool :=
  match Ty.fixedBytesSize? ty with
  | some _ => true
  | none => false

def parseHexNumberLiteralDigits? (text : String) : Option (List Nat) :=
  match text.toList with
  | '0' :: 'x' :: rest => parseSeparatedDigits? hexDigit? rest
  | '0' :: 'X' :: rest => parseSeparatedDigits? hexDigit? rest
  | _ => none

def digitsAllZero : List Nat -> Bool
  | [] => true
  | digit :: rest => digit == 0 && digitsAllZero rest

def hexDigitsToBytes? : List Nat -> Option (List Byte)
  | [] => some []
  | hi :: lo :: rest => do
      let tail ← hexDigitsToBytes? rest
      some ((hi * 16 + lo) :: tail)
  | [_] => none

def rightPadBytesTo (size : Nat) (bytes : List Byte) : List Byte :=
  (bytes.map (fun byte => byte % 256)).take size ++
    List.replicate (size - bytes.length) 0

def stringUtf8Bytes (text : String) : List Byte :=
  text.toUTF8.toList.map UInt8.toNat

def fixedBytesWordFromBytes? (size : Nat) (bytes : List Byte) :
    Option Word :=
  if bytes.length <= size then
    some
      (SolidCore.Solidity.Source.bytesToWordBE
        (rightPadBytesTo size bytes))
  else
    none

def fixedBytesWordFromHexNumber? (size : Nat) (text : String) :
    Option Word := do
  let digits ← parseHexNumberLiteralDigits? text
  if digitsAllZero digits then
    some 0
  else if digits.length == size * 2 then
    let bytes ← hexDigitsToBytes? digits
    some (SolidCore.Solidity.Source.bytesToWordBE bytes)
  else
    none

def fixedBytesWordFromNumber? (size : Nat) (text : String) :
    Option Word :=
  match fixedBytesWordFromHexNumber? size text with
  | some word => some word
  | none => do
      let value ← parseNumberNat? text
      if value == 0 then
        some 0
      else
        none

def Literal.toFixedBytesWord? (size : Nat) : Literal -> Option Word
  | Literal.string text =>
      fixedBytesWordFromBytes? size (text.toList.map Char.toNat)
  | Literal.unicodeString text =>
      fixedBytesWordFromBytes? size (stringUtf8Bytes text)
  | Literal.hexString text => do
      let bytes ← parseHexString? text
      fixedBytesWordFromBytes? size bytes
  | Literal.bytes bytes =>
      fixedBytesWordFromBytes? size bytes
  | Literal.number text =>
      fixedBytesWordFromNumber? size text
  | Literal.unitNumber text unit => do
      let value ← parseUnitNumberNat? text unit
      if value == 0 then
        some 0
      else
        none
  | _ => none

def Literal.isFixedBytesCandidate : Literal -> Bool
  | Literal.string _ => true
  | Literal.unicodeString _ => true
  | Literal.hexString _ => true
  | Literal.bytes _ => true
  | Literal.number text =>
      match parseHexNumberLiteralDigits? text with
      | some _ => true
      | none =>
          match parseNumberNat? text with
          | some value => value == 0
          | none => false
  | Literal.unitNumber _ _ => true
  | _ => false

def Ty.uintBits? : Ty -> Option Nat
  | Ty.uint bits =>
      if bits == 0 then
        some 256
      else if bits % 8 == 0 && bits <= 256 then
        some bits
      else
        none
  | _ => none

def Ty.intBits? : Ty -> Option Nat
  | Ty.int bits =>
      if bits == 0 then
        some 256
      else if bits % 8 == 0 && bits <= 256 then
        some bits
      else
        none
  | _ => none

def Ty.isIntOrUint : Ty -> Bool
  | Ty.uint _ => true
  | Ty.int _ => true
  | _ => false

def Ty.fixedBytesCastWordSourceSize? (targetSize : Nat) (sourceTy : Ty) :
    Option Nat :=
  match Ty.fixedBytesSize? sourceTy with
  | some sourceSize => some sourceSize
  | none =>
      match sourceTy with
      | Ty.uint bits => do
          let sourceBits ← Ty.uintBits? (Ty.uint bits)
          let sourceSize := sourceBits / 8
          if sourceSize == targetSize then some sourceSize else none
      | Ty.int bits => do
          let sourceBits ← Ty.intBits? (Ty.int bits)
          let sourceSize := sourceBits / 8
          if sourceSize == targetSize then some sourceSize else none
      | Ty.address _ =>
          if targetSize == 20 then some 20 else none
      | _ => none

def Ty.allowsUintCastSource? (bits : Nat) (sourceTy : Ty) : Option Unit :=
  match sourceTy with
  | Ty.uint _ => some ()
  | Ty.int _ => some ()
  | Ty.address _ =>
      if bits == 160 then some () else none
  | _ =>
      match Ty.fixedBytesSize? sourceTy with
      | some size =>
          if size * 8 == bits then some () else none
      | none => none

def Ty.allowsIntCastSource? (bits : Nat) (sourceTy : Ty) : Option Unit :=
  match sourceTy with
  | Ty.uint _ => some ()
  | Ty.int _ => some ()
  | _ =>
      match Ty.fixedBytesSize? sourceTy with
      | some size =>
          if size * 8 == bits then some () else none
      | none => none

def Expr.numberLiteralNat? (expr : Expr) : Option Nat := do
  let value ← Expr.numberLiteralRat? expr
  value.exactNat?

def Expr.negatedNumberLiteralNat? : Expr -> Option Nat
  | Expr.unary UnaryOp.neg inner => Expr.numberLiteralNat? inner
  | Expr.call (Expr.typeName _) [Arg.positional expr] =>
      Expr.negatedNumberLiteralNat? expr
  | _ => none

def Expr.toCoreFixedBytesLiteralAs? (ty : Ty) : Expr -> Option CoreExpr
  | Expr.literal literal => do
      let size ← Ty.fixedBytesSize? ty
      let word ← Literal.toFixedBytesWord? size literal
      some (SolidCore.Solidity.Source.Expr.word word)
  | _ => none

def Expr.isFixedBytesLiteralCandidate : Expr -> Bool
  | Expr.literal literal => Literal.isFixedBytesCandidate literal
  | _ => false

def Ty.isAddress : Ty -> Bool
  | Ty.address _ => true
  | _ => false

def addressLiteralFits (value : Nat) : Bool :=
  value < SharedSemantics.External.addressModulus

def Expr.isAddressLiteralCandidate : Expr -> Bool
  | Expr.literal (Literal.address _) => true
  | Expr.literal (Literal.number _) => true
  | Expr.literal (Literal.unitNumber _ _) => true
  | Expr.literal (Literal.string _) => true
  | Expr.literal (Literal.unicodeString _) => true
  | Expr.literal (Literal.hexString _) => true
  | Expr.literal (Literal.bytes _) => true
  | Expr.unary UnaryOp.neg inner => Expr.isAddressLiteralCandidate inner
  | Expr.binary _ lhs rhs =>
      Expr.isAddressLiteralCandidate lhs &&
        Expr.isAddressLiteralCandidate rhs
  | Expr.call (Expr.typeName _) [Arg.positional expr] =>
      Expr.isAddressLiteralCandidate expr
  | _ => false

def Expr.toCoreAddressLiteral? : Expr -> Option CoreExpr
  | Expr.literal (Literal.address value) =>
      some
        (SolidCore.Solidity.Source.Expr.word
          (SharedSemantics.Account.addressWord value))
  | Expr.literal (Literal.number text) => do
      let value ← parseNumberNat? text
      if addressLiteralFits value then
        some (SolidCore.Solidity.Source.Expr.word value)
      else
        none
  | Expr.literal (Literal.unitNumber text unit) => do
      let value ← parseUnitNumberNat? text unit
      if addressLiteralFits value then
        some (SolidCore.Solidity.Source.Expr.word value)
      else
        none
  | _ => none

def Expr.toCorePayableLiteral? : Expr -> Option CoreExpr
  | Expr.literal (Literal.address value) =>
      some
        (SolidCore.Solidity.Source.Expr.word
          (SharedSemantics.Account.addressWord value))
  | Expr.literal (Literal.number text) => do
      let value ← parseNumberNat? text
      if value == 0 then
        some (SolidCore.Solidity.Source.Expr.word 0)
      else
        none
  | Expr.literal (Literal.unitNumber text unit) => do
      let value ← parseUnitNumberNat? text unit
      if value == 0 then
        some (SolidCore.Solidity.Source.Expr.word 0)
      else
        none
  | _ => none

def Expr.isNumberLiteralExpression : Expr -> Bool
  | Expr.literal (Literal.number _) => true
  | Expr.literal (Literal.unitNumber _ _) => true
  | Expr.unary UnaryOp.neg inner => Expr.isNumberLiteralExpression inner
  | Expr.binary _ lhs rhs =>
      Expr.isNumberLiteralExpression lhs &&
        Expr.isNumberLiteralExpression rhs
  | Expr.call (Expr.typeName _) [Arg.positional expr] =>
      Expr.isNumberLiteralExpression expr
  | _ => false

def uintLiteralFits (bits value : Nat) : Bool :=
  value < 2 ^ bits

def intPositiveLiteralFits (bits value : Nat) : Bool :=
  value < 2 ^ (bits - 1)

def intNegativeLiteralFits (bits magnitude : Nat) : Bool :=
  magnitude <= 2 ^ (bits - 1)

def Expr.toCoreNumericLiteralAs? (ty : Ty) (expr : Expr) :
    Option CoreExpr :=
  match Ty.uintBits? ty with
  | some bits => do
      let value ← Expr.numberLiteralNat? expr
      if uintLiteralFits bits value then
        some (SolidCore.Solidity.Source.Expr.word value)
      else
        none
  | none =>
      match Ty.intBits? ty with
      | some bits =>
          match Expr.negatedNumberLiteralNat? expr with
          | some magnitude =>
              if intNegativeLiteralFits bits magnitude then
                some
                  (SolidCore.Solidity.Source.Expr.intWord
                    (SharedSemantics.signedToWord
                      (-(Int.ofNat magnitude))))
              else
                none
          | none => do
              let value ← Expr.numberLiteralNat? expr
              if intPositiveLiteralFits bits value then
                some (SolidCore.Solidity.Source.Expr.intWord value)
              else
                none
      | none => none

def Ty.typeInfoExpr? (ty : Ty) (member : Name) : Option CoreExpr := do
  match Ty.uintBits? ty with
  | some bits =>
      match member with
      | "min" => some (SolidCore.Solidity.Source.Expr.word 0)
      | "max" => some (SolidCore.Solidity.Source.Expr.word ((2 ^ bits) - 1))
      | _ => none
  | none =>
      match Ty.intBits? ty with
      | some bits =>
          match member with
          | "min" =>
              some
                (SolidCore.Solidity.Source.Expr.intWord
                  (2 ^ (bits - 1)))
          | "max" =>
              some
                (SolidCore.Solidity.Source.Expr.intWord
                  ((2 ^ (bits - 1)) - 1))
          | _ => none
      | none =>
          match ty, member with
          | Ty.user path, "name" => do
              let name ← pathLast? path
              some
                (SolidCore.Solidity.Source.Expr.byteArray
                  (name.toList.map Char.toNat))
          | Ty.user path, "creationCode" => do
              let name ← pathLast? path
              some (SolidCore.Solidity.Source.Expr.contractCreationCode name)
          | Ty.user path, "runtimeCode" => do
              let name ← pathLast? path
              some (SolidCore.Solidity.Source.Expr.contractRuntimeCode name)
          | _, _ => none

def Literal.toCoreExpr? : Literal -> Option CoreExpr
  | Literal.bool value =>
      some (SolidCore.Solidity.Source.Expr.word
        (SolidCore.Solidity.Source.boolWord value))
  | Literal.number text => do
      let value ← parseNumberNat? text
      some (SolidCore.Solidity.Source.Expr.word value)
  | Literal.unitNumber text unit => do
      let value ← parseUnitNumberNat? text unit
      some (SolidCore.Solidity.Source.Expr.word value)
  | Literal.address value =>
      some
        (SolidCore.Solidity.Source.Expr.word
          (SharedSemantics.Account.addressWord value))
  | Literal.bytes bytes => some (SolidCore.Solidity.Source.Expr.byteArray bytes)
  | Literal.hexString text => do
      let bytes ← parseHexString? text
      some (SolidCore.Solidity.Source.Expr.byteArray bytes)
  | Literal.string text =>
      some (SolidCore.Solidity.Source.Expr.byteArray
        (text.toList.map Char.toNat))
  | Literal.unicodeString text =>
      some (SolidCore.Solidity.Source.Expr.byteArray
        (stringUtf8Bytes text))

def Literal.abiTy? : Literal -> Option Ty
  | Literal.bool _ => some Ty.bool
  | Literal.number _ => some (Ty.uint 256)
  | Literal.unitNumber _ _ => some (Ty.uint 256)
  | Literal.string _ => some Ty.string
  | Literal.unicodeString _ => some Ty.string
  | Literal.address _ => some (Ty.address false)
  | Literal.bytes _ => some Ty.bytes
  | Literal.hexString _ => some Ty.bytes

def lowLevelCallReturnTy : Ty :=
  Ty.tuple [Ty.bool, Ty.bytes]

def Ty.isBytesConcatArg : Ty -> Bool
  | Ty.bytes => true
  | Ty.string => true
  | Ty.bytesN size => 0 < size && size <= 32
  | Ty.fixedBytes size => 0 < size && size <= 32
  | _ => false

def Tys.allBytesConcatArgs : List Ty -> Bool
  | [] => true
  | ty :: rest => Ty.isBytesConcatArg ty && Tys.allBytesConcatArgs rest

def Ty.isStringConcatArg : Ty -> Bool
  | Ty.string => true
  | _ => false

def Tys.allStringConcatArgs : List Ty -> Bool
  | [] => true
  | ty :: rest => Ty.isStringConcatArg ty && Tys.allStringConcatArgs rest

def CallOptions.lowLevelCallValueLoop? (seenGas seenValue : Bool) :
    List CallOption -> Option (Option Expr)
  | [] => some none
  | CallOption.named name expr :: rest =>
      if name == "gas" then
        if seenGas then
          none
        else
          CallOptions.lowLevelCallValueLoop? true seenValue rest
      else if name == "value" then
        if seenValue then
          none
        else
          match CallOptions.lowLevelCallValueLoop? seenGas true rest with
          | some none => some (some expr)
          | some (some _) => none
          | none => none
      else
        none

def CallOptions.lowLevelCallValue? :
    List CallOption -> Option (Option Expr) :=
  CallOptions.lowLevelCallValueLoop? false false

def CallOptions.lowLevelGasOnlyLoop? (seenGas : Bool) :
    List CallOption -> Option Unit
  | [] => some ()
  | CallOption.named name _ :: rest =>
      if name == "gas" && !seenGas then
        CallOptions.lowLevelGasOnlyLoop? true rest
      else
        none

def CallOptions.lowLevelGasOnly? (options : List CallOption) : Option Unit :=
  CallOptions.lowLevelGasOnlyLoop? false options

def CallOptions.contractCreationValueSaltLoop?
    (seenValue seenSalt : Bool) :
    List CallOption -> Option (Option Expr × Option Expr)
  | [] => some (none, none)
  | CallOption.named name expr :: rest =>
      if name == "value" then
        if seenValue then
          none
        else
          match
            CallOptions.contractCreationValueSaltLoop?
              true seenSalt rest with
          | some (none, salt?) => some (some expr, salt?)
          | _ => none
      else if name == "salt" then
        if seenSalt then
          none
        else
          match
            CallOptions.contractCreationValueSaltLoop?
              seenValue true rest with
          | some (value?, none) => some (value?, some expr)
          | _ => none
      else
        none

def CallOptions.contractCreationValueSalt? :
    List CallOption -> Option (Option Expr × Option Expr) :=
  CallOptions.contractCreationValueSaltLoop? false false

def Ty.contractName? : Ty -> Option Name
  | Ty.user path => pathLast? path
  | _ => none

def Expr.memberCallIsBuiltin? : Expr -> Name -> Bool
  | Expr.ident "abi", name =>
      name == "encode" || name == "decode" ||
        name == "encodePacked" || name == "encodeWithSelector" ||
        name == "encodeWithSignature" || name == "encodeCall"
  | Expr.ident "bytes", "concat" => true
  | Expr.ident "string", "concat" => true
  | _, _ => false

set_option maxHeartbeats 1000000 in
mutual

def Expr.toCore? (storageNames : List Name) : Expr -> Option CoreExpr
  | Expr.literal literal => Literal.toCoreExpr? literal
  | Expr.ident name =>
      if name == "this" then
        some SolidCore.Solidity.Source.Expr.self
      else if stateNameIsStorage name storageNames then
        some (SolidCore.Solidity.Source.Expr.storage name)
      else if stateNameIsImmutable name storageNames then
        some (SolidCore.Solidity.Source.Expr.immutable name)
      else
        some (SolidCore.Solidity.Source.Expr.var name)
  | Expr.member (Expr.typeName ty) member =>
      Ty.typeInfoExpr? ty member
  | Expr.call (Expr.typeName (Ty.address _))
      [Arg.positional (Expr.call (Expr.typeName innerTy)
        [Arg.positional innerExpr])] =>
      match innerTy with
      | Ty.address _ =>
          match Expr.toCoreAddressLiteral? innerExpr with
          | some coreExpr => some coreExpr
          | none =>
              if Expr.isAddressLiteralCandidate innerExpr then
                none
              else
                Expr.toCore? storageNames innerExpr
      | Ty.uint 160 =>
          match Expr.toCoreNumericLiteralAs? innerTy innerExpr with
          | some coreExpr => some coreExpr
          | none =>
              if Expr.isNumberLiteralExpression innerExpr then
                none
              else
                match Expr.abiTy? storageNames innerExpr with
                | some sourceTy => do
                    let _ ← Ty.allowsUintCastSource? 160 sourceTy
                    let coreExpr ← Expr.toCore? storageNames innerExpr
                    some (SolidCore.Solidity.Source.Expr.uintCast
                      160 coreExpr)
                | none => Expr.toCore? storageNames innerExpr
      | Ty.bytesN 20 =>
          match Expr.toCoreFixedBytesLiteralAs? innerTy innerExpr with
          | some coreExpr => some coreExpr
          | none =>
              if Expr.isFixedBytesLiteralCandidate innerExpr then
                none
              else
                match Expr.abiTy? storageNames innerExpr with
                | some Ty.bytes => do
                    let coreExpr ← Expr.toCore? storageNames innerExpr
                    some
                      (SolidCore.Solidity.Source.Expr.fixedBytesFromBytes
                        20 coreExpr)
                | some sourceTy => do
                    let sourceSize ←
                      Ty.fixedBytesCastWordSourceSize? 20 sourceTy
                    let coreExpr ← Expr.toCore? storageNames innerExpr
                    some
                      (SolidCore.Solidity.Source.Expr.fixedBytesCast
                        20 sourceSize coreExpr)
                | none => Expr.toCore? storageNames innerExpr
      | Ty.fixedBytes 20 =>
          match Expr.toCoreFixedBytesLiteralAs? innerTy innerExpr with
          | some coreExpr => some coreExpr
          | none =>
              if Expr.isFixedBytesLiteralCandidate innerExpr then
                none
              else
                match Expr.abiTy? storageNames innerExpr with
                | some Ty.bytes => do
                    let coreExpr ← Expr.toCore? storageNames innerExpr
                    some
                      (SolidCore.Solidity.Source.Expr.fixedBytesFromBytes
                        20 coreExpr)
                | some sourceTy => do
                    let sourceSize ←
                      Ty.fixedBytesCastWordSourceSize? 20 sourceTy
                    let coreExpr ← Expr.toCore? storageNames innerExpr
                    some
                      (SolidCore.Solidity.Source.Expr.fixedBytesCast
                        20 sourceSize coreExpr)
                | none => Expr.toCore? storageNames innerExpr
      | Ty.user _ => do
          let _ ← Ty.toCore? innerTy
          Expr.toCore? storageNames innerExpr
      | _ => none
  | Expr.call (Expr.typeName ty@(Ty.address _)) [Arg.positional expr] =>
      match Expr.toCoreAddressLiteral? expr with
      | some coreExpr => some coreExpr
      | none =>
          if Expr.isAddressLiteralCandidate expr then
            none
          else
            do
            let _ ← Ty.toCore? ty
            Expr.toCore? storageNames expr
  | Expr.call (Expr.typeName ty) [Arg.positional expr] =>
      match Expr.toCoreFixedBytesLiteralAs? ty expr with
      | some coreExpr => some coreExpr
      | none =>
          if Ty.isFixedBytes ty &&
              Expr.isFixedBytesLiteralCandidate expr then
            none
          else
            match Ty.fixedBytesSize? ty with
            | some targetSize => do
                let sourceTy ← Expr.abiTy? storageNames expr
                match sourceTy with
                | Ty.bytes => do
                    let coreExpr ← Expr.toCore? storageNames expr
                    some
                      (SolidCore.Solidity.Source.Expr.fixedBytesFromBytes
                        targetSize coreExpr)
                | _ => do
                    let sourceSize ←
                      Ty.fixedBytesCastWordSourceSize? targetSize sourceTy
                    let coreExpr ← Expr.toCore? storageNames expr
                    some
                      (SolidCore.Solidity.Source.Expr.fixedBytesCast
                        targetSize sourceSize coreExpr)
            | none =>
                match Expr.toCoreNumericLiteralAs? ty expr with
                | some coreExpr => some coreExpr
                | none =>
                    if Ty.isIntOrUint ty &&
                        Expr.isNumberLiteralExpression expr then
                      none
                    else
                      match Ty.uintBits? ty with
                      | some bits =>
                          match Expr.abiTy? storageNames expr with
                          | some sourceTy => do
                              let _ ←
                                Ty.allowsUintCastSource? bits sourceTy
                              let coreExpr ← Expr.toCore? storageNames expr
                              some
                                (SolidCore.Solidity.Source.Expr.uintCast
                                  bits coreExpr)
                          | none => do
                              let _ ← Ty.toCore? ty
                              Expr.toCore? storageNames expr
                      | none =>
                          match Ty.intBits? ty with
                          | some bits =>
                              match Expr.abiTy? storageNames expr with
                              | some sourceTy => do
                                  let _ ←
                                    Ty.allowsIntCastSource? bits sourceTy
                                  let coreExpr ←
                                    Expr.toCore? storageNames expr
                                  some
                                    (SolidCore.Solidity.Source.Expr.intCast
                                      bits coreExpr)
                              | none => do
                                  let _ ← Ty.toCore? ty
                                  Expr.toCore? storageNames expr
                          | none => do
                              let _ ← Ty.toCore? ty
                              Expr.toCore? storageNames expr
  | Expr.member base "balance" => do
      let baseCore ← Expr.toCore? storageNames base
      some (SolidCore.Solidity.Source.Expr.envLookup
        SolidCore.Solidity.Source.EnvLookup.accountBalance baseCore)
  | Expr.member base "code" => do
      let baseCore ← Expr.toCore? storageNames base
      some (SolidCore.Solidity.Source.Expr.envBytesLookup
        SolidCore.Solidity.Source.EnvBytesLookup.accountCode baseCore)
  | Expr.member base "codehash" => do
      let baseCore ← Expr.toCore? storageNames base
      some (SolidCore.Solidity.Source.Expr.envLookup
        SolidCore.Solidity.Source.EnvLookup.accountCodehash baseCore)
  | Expr.member (Expr.ident "msg") "data" =>
      some SolidCore.Solidity.Source.Expr.calldata
  | Expr.member (Expr.ident "msg") "sig" =>
      some SolidCore.Solidity.Source.Expr.msgSig
  | Expr.member (Expr.ident "msg") "sender" =>
      some SolidCore.Solidity.Source.Expr.caller
  | Expr.member (Expr.ident "msg") "value" =>
      some SolidCore.Solidity.Source.Expr.callValue
  | Expr.member (Expr.ident "block") "basefee" =>
      some (SolidCore.Solidity.Source.Expr.env
        SolidCore.Solidity.Source.EnvWord.blockBasefee)
  | Expr.member (Expr.ident "block") "blobbasefee" =>
      some (SolidCore.Solidity.Source.Expr.env
        SolidCore.Solidity.Source.EnvWord.blockBlobbasefee)
  | Expr.member (Expr.ident "block") "chainid" =>
      some (SolidCore.Solidity.Source.Expr.env
        SolidCore.Solidity.Source.EnvWord.blockChainid)
  | Expr.member (Expr.ident "block") "coinbase" =>
      some (SolidCore.Solidity.Source.Expr.env
        SolidCore.Solidity.Source.EnvWord.blockCoinbase)
  | Expr.member (Expr.ident "block") "difficulty" =>
      some (SolidCore.Solidity.Source.Expr.env
        SolidCore.Solidity.Source.EnvWord.blockDifficulty)
  | Expr.member (Expr.ident "block") "gaslimit" =>
      some (SolidCore.Solidity.Source.Expr.env
        SolidCore.Solidity.Source.EnvWord.blockGaslimit)
  | Expr.member (Expr.ident "block") "number" =>
      some (SolidCore.Solidity.Source.Expr.env
        SolidCore.Solidity.Source.EnvWord.blockNumber)
  | Expr.member (Expr.ident "block") "prevrandao" =>
      some (SolidCore.Solidity.Source.Expr.env
        SolidCore.Solidity.Source.EnvWord.blockPrevrandao)
  | Expr.member (Expr.ident "block") "timestamp" =>
      some (SolidCore.Solidity.Source.Expr.env
        SolidCore.Solidity.Source.EnvWord.blockTimestamp)
  | Expr.member (Expr.ident "tx") "gasprice" =>
      some (SolidCore.Solidity.Source.Expr.env
        SolidCore.Solidity.Source.EnvWord.txGasprice)
  | Expr.member (Expr.ident "tx") "origin" =>
      some (SolidCore.Solidity.Source.Expr.env
        SolidCore.Solidity.Source.EnvWord.txOrigin)
  | Expr.call (Expr.ident "gasleft") [] =>
      some (SolidCore.Solidity.Source.Expr.env
        SolidCore.Solidity.Source.EnvWord.gasleft)
  | Expr.newExpr Ty.bytes [Arg.positional lengthExpr] => do
      let lengthCore ← Expr.toCore? storageNames lengthExpr
      some (SolidCore.Solidity.Source.Expr.newBytes lengthCore)
  | Expr.newExpr (Ty.array elementTy none)
      [Arg.positional lengthExpr] => do
      let coreElementTy ← Ty.toCore? elementTy
      let lengthCore ← Expr.toCore? storageNames lengthExpr
      some
        (SolidCore.Solidity.Source.Expr.newDynamicArray
          coreElementTy lengthCore)
  | Expr.newExpr ty args => do
      let contractName ← Ty.contractName? ty
      let (coreTys, coreExprs) ← Args.toAbiEncode? storageNames args
      some
        (SolidCore.Solidity.Source.Expr.contractCreate
          contractName
          (SolidCore.Solidity.Source.Expr.abiEncode coreTys coreExprs)
          (SolidCore.Solidity.Source.Expr.word 0)
          none)
  | Expr.callWithOptions (Expr.newExpr ty []) options args => do
      let contractName ← Ty.contractName? ty
      let (valueCore?, saltCore?) ←
        CallOptions.contractCreationValueSaltCore? storageNames options
      let valueCore :=
        match valueCore? with
        | some valueCore => valueCore
        | none => SolidCore.Solidity.Source.Expr.word 0
      let (coreTys, coreExprs) ← Args.toAbiEncode? storageNames args
      some
        (SolidCore.Solidity.Source.Expr.contractCreate
          contractName
          (SolidCore.Solidity.Source.Expr.abiEncode coreTys coreExprs)
          valueCore saltCore?)
  | Expr.call (Expr.member target "call") [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.toCore? storageNames payload
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.call
          targetCore payloadCore (SolidCore.Solidity.Source.Expr.word 0))
  | Expr.callWithOptions (Expr.member target "call")
      options [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.toCore? storageNames payload
      let valueCore ← CallOptions.lowLevelCallValueCore? storageNames options
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.call
          targetCore payloadCore valueCore)
  | Expr.call (Expr.member target "staticcall") [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.toCore? storageNames payload
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.staticcall
          targetCore payloadCore (SolidCore.Solidity.Source.Expr.word 0))
  | Expr.callWithOptions (Expr.member target "staticcall")
      options [Arg.positional payload] => do
      let _ ← CallOptions.lowLevelGasOnly? options
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.toCore? storageNames payload
      let valueCore ← CallOptions.lowLevelCallValueCore? storageNames options
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.staticcall
          targetCore payloadCore valueCore)
  | Expr.call (Expr.member target "delegatecall") [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.toCore? storageNames payload
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.delegatecall
          targetCore payloadCore (SolidCore.Solidity.Source.Expr.word 0))
  | Expr.callWithOptions (Expr.member target "delegatecall")
      options [Arg.positional payload] => do
      let _ ← CallOptions.lowLevelGasOnly? options
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.toCore? storageNames payload
      let valueCore ← CallOptions.lowLevelCallValueCore? storageNames options
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.delegatecall
          targetCore payloadCore valueCore)
  | Expr.call (Expr.member target "send") [Arg.positional value] => do
      let targetCore ← Expr.toCore? storageNames target
      let valueCore ← Expr.toCore? storageNames value
      some
        (SolidCore.Solidity.Source.Expr.index
          (SolidCore.Solidity.Source.Expr.lowLevelCall
            SolidCore.Solidity.Source.LowLevelCallKind.call
            targetCore
            (SolidCore.Solidity.Source.Expr.byteArray [])
            valueCore)
          (SolidCore.Solidity.Source.Expr.word 0))
  | Expr.call (Expr.member (Expr.ident "abi") "encode") args => do
      let (tys, exprs) ← Args.toAbiEncode? storageNames args
      some (SolidCore.Solidity.Source.Expr.abiEncode tys exprs)
  | Expr.call (Expr.member (Expr.ident "abi") "decode")
      [Arg.positional data, Arg.positional typesExpr] => do
      let (tys, dataCore) ← Expr.toAbiDecode? storageNames data typesExpr
      some (SolidCore.Solidity.Source.Expr.abiDecode tys dataCore)
  | Expr.call (Expr.member (Expr.ident "abi") "encodePacked") args => do
      let (tys, exprs) ← Args.toAbiEncode? storageNames args
      some (SolidCore.Solidity.Source.Expr.abiEncodePacked tys exprs)
  | Expr.call (Expr.member (Expr.ident "abi") "encodeWithSelector")
      (Arg.positional selector :: args) => do
      match Expr.abiTy? storageNames selector with
      | some (Ty.bytesN 4) => some ()
      | some (Ty.fixedBytes 4) => some ()
      | _ => none
      let selectorCore ← Expr.toCore? storageNames selector
      let (tys, exprs) ← Args.toAbiEncode? storageNames args
      some
        (SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
          selectorCore tys exprs)
  | Expr.call (Expr.member (Expr.ident "abi") "encodeWithSignature")
      (Arg.positional (Expr.literal (Literal.string signature)) :: args) => do
      let (tys, exprs) ← Args.toAbiEncode? storageNames args
      some
        (SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
          (SolidCore.Solidity.Source.Expr.word
            (SolidCore.Solidity.Source.ABI.selectorFromSignature
              signature))
          tys exprs)
  | Expr.call (Expr.member (Expr.ident "abi") "encodeWithSignature")
      (Arg.positional signature :: args) => do
      let signatureCore ← Expr.toCore? storageNames signature
      let (tys, exprs) ← Args.toAbiEncode? storageNames args
      some
        (SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
          (SolidCore.Solidity.Source.Expr.fixedBytesCast 4 32
            (SolidCore.Solidity.Source.Expr.keccak256 signatureCore))
          tys exprs)
  | Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
      [Arg.positional functionPointer, Arg.positional (Expr.tuple items)] => do
      let functionName ← Expr.functionPointerName? functionPointer
      let (sourceTys, coreTys, coreExprs) ←
        TupleItems.toAbiEncodeSource? storageNames items
      let signature ← externalFunctionSignature? functionName sourceTys
      some
        (SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
          (SolidCore.Solidity.Source.Expr.word
            (SolidCore.Solidity.Source.ABI.selectorFromSignature
              signature))
          coreTys coreExprs)
  | Expr.call (Expr.ident "blockhash") [Arg.positional number] => do
      let numberCore ← Expr.toCore? storageNames number
      some (SolidCore.Solidity.Source.Expr.envLookup
        SolidCore.Solidity.Source.EnvLookup.blockhash numberCore)
  | Expr.call (Expr.ident "blobhash") [Arg.positional index] => do
      let indexCore ← Expr.toCore? storageNames index
      some (SolidCore.Solidity.Source.Expr.envLookup
        SolidCore.Solidity.Source.EnvLookup.blobhash indexCore)
  | Expr.call (Expr.ident "addmod")
      [Arg.positional lhs, Arg.positional rhs, Arg.positional modulus] => do
      let lhsCore ← Expr.toCore? storageNames lhs
      let rhsCore ← Expr.toCore? storageNames rhs
      let modulusCore ← Expr.toCore? storageNames modulus
      some (SolidCore.Solidity.Source.Expr.addMod
        lhsCore rhsCore modulusCore)
  | Expr.call (Expr.ident "mulmod")
      [Arg.positional lhs, Arg.positional rhs, Arg.positional modulus] => do
      let lhsCore ← Expr.toCore? storageNames lhs
      let rhsCore ← Expr.toCore? storageNames rhs
      let modulusCore ← Expr.toCore? storageNames modulus
      some (SolidCore.Solidity.Source.Expr.mulMod
        lhsCore rhsCore modulusCore)
  | Expr.call (Expr.ident "keccak256") [Arg.positional bytes] => do
      let bytesCore ← Expr.toCore? storageNames bytes
      some (SolidCore.Solidity.Source.Expr.keccak256 bytesCore)
  | Expr.call (Expr.ident "erc7201") [Arg.positional id] => do
      let idCore ← Expr.toCore? storageNames id
      some (SolidCore.Solidity.Source.Expr.erc7201 idCore)
  | Expr.call (Expr.ident "sha256") [Arg.positional bytes] => do
      let bytesCore ← Expr.toCore? storageNames bytes
      some
        (SolidCore.Solidity.Source.Expr.externalHash
          SolidCore.Solidity.Source.ExternalHashKind.sha256 bytesCore)
  | Expr.call (Expr.ident "ripemd160") [Arg.positional bytes] => do
      let bytesCore ← Expr.toCore? storageNames bytes
      some
        (SolidCore.Solidity.Source.Expr.externalHash
          SolidCore.Solidity.Source.ExternalHashKind.ripemd160 bytesCore)
  | Expr.call (Expr.ident "ecrecover")
      [ Arg.positional digest
      , Arg.positional v
      , Arg.positional r
      , Arg.positional s ] => do
      let digestCore ← Expr.toCore? storageNames digest
      let vCore ← Expr.toCore? storageNames v
      let rCore ← Expr.toCore? storageNames r
      let sCore ← Expr.toCore? storageNames s
      some
        (SolidCore.Solidity.Source.Expr.ecrecover
          digestCore vCore rCore sCore)
  | Expr.call (Expr.member (Expr.ident "bytes") "concat") args => do
      let (sourceTys, coreTys, coreExprs) ←
        Args.toAbiEncodeSource? storageNames args
      if Tys.allBytesConcatArgs sourceTys then
        some (SolidCore.Solidity.Source.Expr.abiEncodePacked
          coreTys coreExprs)
      else
        none
  | Expr.call (Expr.member (Expr.ident "string") "concat") args => do
      let (sourceTys, coreTys, coreExprs) ←
        Args.toAbiEncodeSource? storageNames args
      if Tys.allStringConcatArgs sourceTys then
        some (SolidCore.Solidity.Source.Expr.abiEncodePacked
          coreTys coreExprs)
      else
        none
  | Expr.member (Expr.ident name) "length" =>
      if stateNameIsStorage name storageNames then
        some (SolidCore.Solidity.Source.Expr.storage name)
      else
        do
        let baseCore ← Expr.toCore? storageNames (Expr.ident name)
        some (SolidCore.Solidity.Source.Expr.length baseCore)
  | Expr.member base "length" =>
      match Expr.abiTy? storageNames base with
      | some ty =>
          match Ty.fixedBytesSize? ty with
          | some size => some (SolidCore.Solidity.Source.Expr.word size)
          | none => do
              let baseCore ← Expr.toCore? storageNames base
              some (SolidCore.Solidity.Source.Expr.length baseCore)
      | none => do
          let baseCore ← Expr.toCore? storageNames base
          some (SolidCore.Solidity.Source.Expr.length baseCore)
  | Expr.index (Expr.ident name) index =>
      if stateNameIsStorage name storageNames then
        do
        let indexCore ← Expr.toCore? storageNames index
        some (SolidCore.Solidity.Source.Expr.storageIndex name indexCore)
      else
        do
        let baseCore ← Expr.toCore? storageNames (Expr.ident name)
        let indexCore ← Expr.toCore? storageNames index
        some (SolidCore.Solidity.Source.Expr.index baseCore indexCore)
  | Expr.index base index =>
      match Expr.abiTy? storageNames base with
      | some ty =>
          match Ty.fixedBytesSize? ty with
          | some size => do
              let baseCore ← Expr.toCore? storageNames base
              let indexCore ← Expr.toCore? storageNames index
              some
                (SolidCore.Solidity.Source.Expr.fixedBytesIndex
                  size baseCore indexCore)
          | none => do
              let baseCore ← Expr.toCore? storageNames base
              let indexCore ← Expr.toCore? storageNames index
              some (SolidCore.Solidity.Source.Expr.index baseCore indexCore)
      | none => do
          let baseCore ← Expr.toCore? storageNames base
          let indexCore ← Expr.toCore? storageNames index
          some (SolidCore.Solidity.Source.Expr.index baseCore indexCore)
  | Expr.slice base start stop => do
      let baseCore ← Expr.toCore? storageNames base
      let startCore? ←
        match start with
        | some expr => do
            let core ← Expr.toCore? storageNames expr
            some (some core)
        | none => some none
      let stopCore? ←
        match stop with
        | some expr => do
            let core ← Expr.toCore? storageNames expr
            some (some core)
        | none => some none
      some (SolidCore.Solidity.Source.Expr.slice
        baseCore startCore? stopCore?)
  | Expr.enumFromUInt maxValue expr => do
      let coreExpr ← Expr.toCore? storageNames expr
      some (SolidCore.Solidity.Source.Expr.enumFromUInt maxValue coreExpr)
  | Expr.unary UnaryOp.preIncrement target => do
      let targetCore ← Expr.toCoreLValue? storageNames target
      some (SolidCore.Solidity.Source.Expr.preIncrement targetCore.toExpr)
  | Expr.unary UnaryOp.preDecrement target => do
      let targetCore ← Expr.toCoreLValue? storageNames target
      some (SolidCore.Solidity.Source.Expr.preDecrement targetCore.toExpr)
  | Expr.unary UnaryOp.postIncrement target => do
      let targetCore ← Expr.toCoreLValue? storageNames target
      some (SolidCore.Solidity.Source.Expr.postIncrement targetCore.toExpr)
  | Expr.unary UnaryOp.postDecrement target => do
      let targetCore ← Expr.toCoreLValue? storageNames target
      some (SolidCore.Solidity.Source.Expr.postDecrement targetCore.toExpr)
  | Expr.unary op expr => do
      let coreOp ← UnaryOp.toCore? op
      let coreExpr ← Expr.toCore? storageNames expr
      some (SolidCore.Solidity.Source.Expr.unary coreOp coreExpr)
  | Expr.assign lhs AssignOp.assign rhs => do
      let lhsCore ← Expr.toCoreLValue? storageNames lhs
      let rhsCore ← Expr.toCore? storageNames rhs
      some (SolidCore.Solidity.Source.Expr.assignExpr lhsCore.toExpr rhsCore)
  | Expr.assign lhs op rhs => do
      let lhsCore ← Expr.toCoreLValue? storageNames lhs
      let coreOp ← AssignOp.toCoreBinary? op
      let rhsCore ← Expr.toCore? storageNames rhs
      some
        (SolidCore.Solidity.Source.Expr.assignOpExpr
          lhsCore.toExpr coreOp rhsCore)
  | expr@(Expr.binary op lhs rhs) =>
      match Expr.numberLiteralRat? expr with
      | some value => do
          let word ← value.exactNat?
          some (SolidCore.Solidity.Source.Expr.word word)
      | none =>
          match Expr.numberLiteralBool? expr with
          | some value =>
              some
                (SolidCore.Solidity.Source.Expr.word
                  (numberLiteralBoolWord value))
          | none => do
              let coreOp ← BinaryOp.toCore? op
              let lhsCore ← Expr.toCore? storageNames lhs
              let rhsCore ← Expr.toCore? storageNames rhs
              some (SolidCore.Solidity.Source.Expr.binary
                coreOp lhsCore rhsCore)
  | Expr.ternary cond thenExpr elseExpr => do
      let condCore ← Expr.toCore? storageNames cond
      let thenCore ← Expr.toCore? storageNames thenExpr
      let elseCore ← Expr.toCore? storageNames elseExpr
      some (SolidCore.Solidity.Source.Expr.ternary
        condCore thenCore elseCore)
  | Expr.tuple items => do
      let coreExprs ← TupleItems.toCoreExprs? storageNames items
      some (SolidCore.Solidity.Source.Expr.tuple coreExprs)
  | Expr.array exprs => do
      let coreExprs ← Expr.listToCore? storageNames exprs
      some (SolidCore.Solidity.Source.Expr.fixedArray coreExprs)
  | Expr.payableConversion
      (Expr.call (Expr.typeName (Ty.address _))
        [Arg.positional (Expr.call (Expr.typeName innerTy)
          [Arg.positional innerExpr])]) =>
      match innerTy with
      | Ty.address _ =>
          match Expr.toCoreAddressLiteral? innerExpr with
          | some coreExpr => some coreExpr
          | none =>
              if Expr.isAddressLiteralCandidate innerExpr then
                none
              else
                Expr.toCore? storageNames innerExpr
      | Ty.uint 160 =>
          match Expr.toCoreNumericLiteralAs? innerTy innerExpr with
          | some coreExpr => some coreExpr
          | none =>
              if Expr.isNumberLiteralExpression innerExpr then
                none
              else
                match Expr.abiTy? storageNames innerExpr with
                | some sourceTy => do
                    let _ ← Ty.allowsUintCastSource? 160 sourceTy
                    let coreExpr ← Expr.toCore? storageNames innerExpr
                    some (SolidCore.Solidity.Source.Expr.uintCast
                      160 coreExpr)
                | none => Expr.toCore? storageNames innerExpr
      | Ty.bytesN 20 =>
          match Expr.toCoreFixedBytesLiteralAs? innerTy innerExpr with
          | some coreExpr => some coreExpr
          | none =>
              if Expr.isFixedBytesLiteralCandidate innerExpr then
                none
              else
                match Expr.abiTy? storageNames innerExpr with
                | some Ty.bytes => do
                    let coreExpr ← Expr.toCore? storageNames innerExpr
                    some
                      (SolidCore.Solidity.Source.Expr.fixedBytesFromBytes
                        20 coreExpr)
                | some sourceTy => do
                    let sourceSize ←
                      Ty.fixedBytesCastWordSourceSize? 20 sourceTy
                    let coreExpr ← Expr.toCore? storageNames innerExpr
                    some
                      (SolidCore.Solidity.Source.Expr.fixedBytesCast
                        20 sourceSize coreExpr)
                | none => Expr.toCore? storageNames innerExpr
      | Ty.fixedBytes 20 =>
          match Expr.toCoreFixedBytesLiteralAs? innerTy innerExpr with
          | some coreExpr => some coreExpr
          | none =>
              if Expr.isFixedBytesLiteralCandidate innerExpr then
                none
              else
                match Expr.abiTy? storageNames innerExpr with
                | some Ty.bytes => do
                    let coreExpr ← Expr.toCore? storageNames innerExpr
                    some
                      (SolidCore.Solidity.Source.Expr.fixedBytesFromBytes
                        20 coreExpr)
                | some sourceTy => do
                    let sourceSize ←
                      Ty.fixedBytesCastWordSourceSize? 20 sourceTy
                    let coreExpr ← Expr.toCore? storageNames innerExpr
                    some
                      (SolidCore.Solidity.Source.Expr.fixedBytesCast
                        20 sourceSize coreExpr)
                | none => Expr.toCore? storageNames innerExpr
      | Ty.user _ => do
          let _ ← Ty.toCore? innerTy
          Expr.toCore? storageNames innerExpr
      | _ => none
  | Expr.payableConversion
      (Expr.call (Expr.typeName (Ty.address _)) [Arg.positional innerExpr]) =>
      match Expr.toCoreAddressLiteral? innerExpr with
      | some coreExpr => some coreExpr
      | none =>
          if Expr.isAddressLiteralCandidate innerExpr then
            none
          else
            Expr.toCore? storageNames innerExpr
  | Expr.payableConversion expr =>
      match Expr.toCorePayableLiteral? expr with
      | some coreExpr => some coreExpr
      | none =>
          if Expr.isAddressLiteralCandidate expr then
            none
          else
            Expr.toCore? storageNames expr
  | _ => none
termination_by expr => (sizeOf expr, 0)
decreasing_by
  all_goals simp_wf
  all_goals omega

def CoreExpr.zero : CoreExpr :=
  SolidCore.Solidity.Source.Expr.word 0

def CoreExpr.ignoreThen (ignored result : CoreExpr) : CoreExpr :=
  SolidCore.Solidity.Source.Expr.binary
    SolidCore.Solidity.Source.BinaryOp.add
    (SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.mul
      ignored
      CoreExpr.zero)
    result

def CoreExpr.returnThenIgnore (result ignored : CoreExpr) : CoreExpr :=
  SolidCore.Solidity.Source.Expr.binary
    SolidCore.Solidity.Source.BinaryOp.add
    result
    (SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.mul
      ignored
      CoreExpr.zero)

def CallOptions.lowLevelCallValueCore? (storageNames : List Name) :
    List CallOption -> Option CoreExpr
  | [] => some CoreExpr.zero
  | [CallOption.named "gas" gas] => do
      let gasCore ← Expr.toCore? storageNames gas
      some (CoreExpr.ignoreThen gasCore CoreExpr.zero)
  | [CallOption.named "value" value] =>
      Expr.toCore? storageNames value
  | [CallOption.named "gas" gas, CallOption.named "value" value] => do
      let gasCore ← Expr.toCore? storageNames gas
      let valueCore ← Expr.toCore? storageNames value
      some (CoreExpr.ignoreThen gasCore valueCore)
  | [CallOption.named "value" value, CallOption.named "gas" gas] => do
      let valueCore ← Expr.toCore? storageNames value
      let gasCore ← Expr.toCore? storageNames gas
      some (CoreExpr.returnThenIgnore valueCore gasCore)
  | _ => none
termination_by options => (sizeOf options, 0)

def CallOptions.contractCreationValueSaltCore? (storageNames : List Name) :
    List CallOption -> Option (Option CoreExpr × Option CoreExpr)
  | [] => some (none, none)
  | [CallOption.named "value" value] => do
      let valueCore ← Expr.toCore? storageNames value
      some (some valueCore, none)
  | [CallOption.named "salt" salt] => do
      let saltCore ← Expr.toCore? storageNames salt
      some (none, some saltCore)
  | [CallOption.named "value" value, CallOption.named "salt" salt] => do
      let valueCore ← Expr.toCore? storageNames value
      let saltCore ← Expr.toCore? storageNames salt
      some (some valueCore, some saltCore)
  | [CallOption.named "salt" salt, CallOption.named "value" value] => do
      let saltCore ← Expr.toCore? storageNames salt
      let valueCore ← Expr.toCore? storageNames value
      some (some valueCore, some saltCore)
  | _ => none
termination_by options => (sizeOf options, 0)

def Args.positionalToCoreExprs? (storageNames : List Name) :
    List Arg -> Option (List CoreExpr)
  | [] => some []
  | Arg.positional expr :: rest => do
      let head ← Expr.toCore? storageNames expr
      let tail ← Args.positionalToCoreExprs? storageNames rest
      some (head :: tail)
  | Arg.named _ _ :: _ => none
termination_by args => (sizeOf args, 0)

def Expr.listToCore? (storageNames : List Name) :
    List Expr -> Option (List CoreExpr)
  | [] => some []
  | expr :: rest => do
      let head ← Expr.toCore? storageNames expr
      let tail ← Expr.listToCore? storageNames rest
      some (head :: tail)
termination_by exprs => (sizeOf exprs, 1)

def Expr.arrayLiteralElementsMatch? (storageNames : List Name)
    (canonical : String) : List Expr -> Option Unit
  | [] => some ()
  | expr :: rest => do
      let ty ← Expr.abiTy? storageNames expr
      let exprCanonical ← Ty.abiCanonical? ty
      if exprCanonical == canonical then
        Expr.arrayLiteralElementsMatch? storageNames canonical rest
      else
        none
termination_by exprs => (sizeOf exprs, 1)

def Expr.arrayLiteralTy? (storageNames : List Name) :
    List Expr -> Option Ty
  | [] => none
  | first :: rest => do
      let firstTy ← Expr.abiTy? storageNames first
      let canonical ← Ty.abiCanonical? firstTy
      let _ ← Expr.arrayLiteralElementsMatch? storageNames canonical rest
      some (Ty.array firstTy (some (first :: rest).length))
termination_by exprs => (sizeOf exprs, 1)

def Expr.abiTy? (storageNames : List Name) : Expr -> Option Ty
  | Expr.literal literal => Literal.abiTy? literal
  | Expr.call (Expr.typeName ty) [_] => do
      let _ ← Ty.toCore? ty
      some ty
  | Expr.payableConversion _ => some (Ty.address true)
  | Expr.member (Expr.ident "msg") "data" => some Ty.bytes
  | Expr.member (Expr.ident "msg") "sig" => some (Ty.bytesN 4)
  | Expr.member (Expr.ident "msg") "sender" => some (Ty.address false)
  | Expr.member (Expr.ident "msg") "value" => some (Ty.uint 256)
  | Expr.member (Expr.ident "block") "basefee" => some (Ty.uint 256)
  | Expr.member (Expr.ident "block") "blobbasefee" => some (Ty.uint 256)
  | Expr.member (Expr.ident "block") "chainid" => some (Ty.uint 256)
  | Expr.member (Expr.ident "block") "coinbase" => some (Ty.address true)
  | Expr.member (Expr.ident "block") "difficulty" => some (Ty.uint 256)
  | Expr.member (Expr.ident "block") "gaslimit" => some (Ty.uint 256)
  | Expr.member (Expr.ident "block") "number" => some (Ty.uint 256)
  | Expr.member (Expr.ident "block") "prevrandao" => some (Ty.uint 256)
  | Expr.member (Expr.ident "block") "timestamp" => some (Ty.uint 256)
  | Expr.member (Expr.ident "tx") "gasprice" => some (Ty.uint 256)
  | Expr.member (Expr.ident "tx") "origin" => some (Ty.address false)
  | Expr.call (Expr.ident "gasleft") [] => some (Ty.uint 256)
  | Expr.call (Expr.ident "blockhash") [_] => some (Ty.bytesN 32)
  | Expr.call (Expr.ident "blobhash") [_] => some (Ty.bytesN 32)
  | Expr.call (Expr.ident "addmod") [_, _, _] => some (Ty.uint 256)
  | Expr.call (Expr.ident "mulmod") [_, _, _] => some (Ty.uint 256)
  | Expr.call (Expr.ident "keccak256") [_] => some (Ty.bytesN 32)
  | Expr.call (Expr.ident "erc7201") [_] => some (Ty.uint 256)
  | Expr.call (Expr.ident "sha256") [_] => some (Ty.bytesN 32)
  | Expr.call (Expr.ident "ripemd160") [_] => some (Ty.bytesN 20)
  | Expr.call (Expr.ident "ecrecover") [_, _, _, _] =>
      some (Ty.address false)
  | Expr.member (Expr.typeName (Ty.user _)) "name" => some Ty.string
  | Expr.member (Expr.typeName (Ty.user _)) "creationCode" => some Ty.bytes
  | Expr.member (Expr.typeName (Ty.user _)) "runtimeCode" => some Ty.bytes
  | Expr.newExpr Ty.bytes [Arg.positional _] => some Ty.bytes
  | Expr.newExpr (Ty.array elementTy none) [Arg.positional _] =>
      some (Ty.array elementTy none)
  | Expr.newExpr ty _ => do
      let _ ← Ty.contractName? ty
      some ty
  | Expr.callWithOptions (Expr.newExpr ty []) options _ => do
      let _ ← Ty.contractName? ty
      let _ ← CallOptions.contractCreationValueSalt? options
      some ty
  | Expr.call (Expr.member _ "call") [Arg.positional _] =>
      some lowLevelCallReturnTy
  | Expr.callWithOptions (Expr.member _ "call")
      options [Arg.positional _] => do
      let _ ← CallOptions.lowLevelCallValue? options
      some lowLevelCallReturnTy
  | Expr.call (Expr.member _ "staticcall") [Arg.positional _] =>
      some lowLevelCallReturnTy
  | Expr.callWithOptions (Expr.member _ "staticcall")
      options [Arg.positional _] => do
      let _ ← CallOptions.lowLevelGasOnly? options
      some lowLevelCallReturnTy
  | Expr.call (Expr.member _ "delegatecall") [Arg.positional _] =>
      some lowLevelCallReturnTy
  | Expr.callWithOptions (Expr.member _ "delegatecall")
      options [Arg.positional _] => do
      let _ ← CallOptions.lowLevelGasOnly? options
      some lowLevelCallReturnTy
  | Expr.call (Expr.member _ "send") [Arg.positional _] => some Ty.bool
  | Expr.call (Expr.member (Expr.ident "abi") "encode") _ => some Ty.bytes
  | Expr.call (Expr.member (Expr.ident "abi") "decode")
      [_, Arg.positional typesExpr] => do
      let tys ← Expr.abiDecodeSourceTypes? typesExpr
      match tys with
      | [] => none
      | [ty] => some ty
      | _ => some (Ty.tuple tys)
  | Expr.call (Expr.member (Expr.ident "abi") "encodePacked") _ =>
      some Ty.bytes
  | Expr.call (Expr.member (Expr.ident "abi") "encodeWithSelector") _ =>
      some Ty.bytes
  | Expr.call (Expr.member (Expr.ident "abi") "encodeWithSignature") _ =>
      some Ty.bytes
  | Expr.call (Expr.member (Expr.ident "abi") "encodeCall") _ =>
      some Ty.bytes
  | Expr.call (Expr.member (Expr.ident "bytes") "concat") _ => some Ty.bytes
  | Expr.call (Expr.member (Expr.ident "string") "concat") _ => some Ty.string
  | Expr.enumFromUInt _ _ => some (Ty.uint 8)
  | Expr.index base _ => do
      let baseTy ← Expr.abiTy? storageNames base
      match Ty.fixedBytesSize? baseTy with
      | some _ => some (Ty.bytesN 1)
      | none =>
          match baseTy with
          | Ty.bytes => some (Ty.bytesN 1)
          | Ty.array elementTy _ => some elementTy
          | _ => none
  | Expr.member base "balance" => do
      let _ ← Expr.abiTy? storageNames base
      some (Ty.uint 256)
  | Expr.member base "code" => do
      let _ ← Expr.abiTy? storageNames base
      some Ty.bytes
  | Expr.member base "codehash" => do
      let _ ← Expr.abiTy? storageNames base
      some (Ty.bytesN 32)
  | Expr.member base "length" => do
      let _ ← Expr.abiTy? storageNames base
      some (Ty.uint 256)
  | Expr.unary UnaryOp.logicalNot _ => some Ty.bool
  | Expr.unary UnaryOp.bitNot expr => Expr.abiTy? storageNames expr
  | Expr.unary UnaryOp.neg expr => Expr.abiTy? storageNames expr
  | Expr.binary op lhs _ =>
      match op with
      | BinaryOp.lt | BinaryOp.gt | BinaryOp.le | BinaryOp.ge
      | BinaryOp.eq | BinaryOp.ne | BinaryOp.boolAnd | BinaryOp.boolOr =>
          some Ty.bool
      | _ => Expr.abiTy? storageNames lhs
  | Expr.ternary _ thenExpr _ => Expr.abiTy? storageNames thenExpr
  | Expr.array exprs => Expr.arrayLiteralTy? storageNames exprs
  | Expr.slice _ _ _ => some Ty.bytes
  | _ => none
termination_by expr => (sizeOf expr, 0)

def Expr.toAbiEncodeArg? (storageNames : List Name) (expr : Expr) :
    Option (CoreTy × CoreExpr) := do
  let ty ← Expr.abiTy? storageNames expr
  let coreTy ← Ty.toCore? ty
  let coreExpr ← Expr.toCore? storageNames expr
  some (coreTy, coreExpr)
termination_by (sizeOf expr, 2)

def Args.toAbiEncode? (storageNames : List Name) :
    List Arg -> Option (List CoreTy × List CoreExpr)
  | [] => some ([], [])
  | Arg.positional expr :: rest => do
      let (ty, coreExpr) ← Expr.toAbiEncodeArg? storageNames expr
      let (tys, coreExprs) ← Args.toAbiEncode? storageNames rest
      some (ty :: tys, coreExpr :: coreExprs)
  | Arg.named _ _ :: _ => none
termination_by args => (sizeOf args, 0)

def Expr.toAbiEncodeSourceArg? (storageNames : List Name) (expr : Expr) :
    Option (Ty × CoreTy × CoreExpr) := do
  let ty ← Expr.abiTy? storageNames expr
  let coreTy ← Ty.toCore? ty
  let coreExpr ← Expr.toCore? storageNames expr
  some (ty, coreTy, coreExpr)
termination_by (sizeOf expr, 2)

def Args.toAbiEncodeSource? (storageNames : List Name) :
    List Arg -> Option (List Ty × List CoreTy × List CoreExpr)
  | [] => some ([], [], [])
  | Arg.positional expr :: rest => do
      let (sourceTy, coreTy, coreExpr) ←
        Expr.toAbiEncodeSourceArg? storageNames expr
      let (sourceTys, coreTys, coreExprs) ←
        Args.toAbiEncodeSource? storageNames rest
      some (sourceTy :: sourceTys, coreTy :: coreTys, coreExpr :: coreExprs)
  | Arg.named _ _ :: _ => none
termination_by args => (sizeOf args, 0)

def TupleItems.toAbiEncodeSource? (storageNames : List Name) :
    List TupleItem -> Option (List Ty × List CoreTy × List CoreExpr)
  | [] => some ([], [], [])
  | TupleItem.value expr :: rest => do
      let (sourceTy, coreTy, coreExpr) ←
        Expr.toAbiEncodeSourceArg? storageNames expr
      let (sourceTys, coreTys, coreExprs) ←
        TupleItems.toAbiEncodeSource? storageNames rest
      some (sourceTy :: sourceTys, coreTy :: coreTys, coreExpr :: coreExprs)
  | TupleItem.hole :: _ => none
termination_by items => (sizeOf items, 0)

def externalFunctionSignature? (name : Name) (argTys : List Ty) :
    Option String := do
  let canonicals ← Ty.listAbiCanonical? argTys
  some (name ++ "(" ++ joinStringsWith "," canonicals ++ ")")

def Expr.functionPointerName? : Expr -> Option Name
  | Expr.member _ name =>
      if name == "call" || name == "staticcall" ||
          name == "delegatecall" || name == "send" ||
          name == "transfer" then
        none
      else
        some name
  | _ => none

def Expr.toExternalCall? (storageNames : List Name) :
    Expr -> Option (CoreExpr × CoreExpr × CoreExpr)
  | Expr.call (Expr.member target name) args => do
      if name == "call" || name == "staticcall" ||
          name == "delegatecall" || name == "send" ||
          name == "transfer" then
        none
      else
        some ()
      if Expr.memberCallIsBuiltin? target name then
        none
      else
        some ()
      let targetCore ← Expr.toCore? storageNames target
      let (sourceTys, coreTys, coreExprs) ←
        Args.toAbiEncodeSource? storageNames args
      let signature ← externalFunctionSignature? name sourceTys
      let callData :=
        SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
          (SolidCore.Solidity.Source.Expr.word
            (SolidCore.Solidity.Source.ABI.selectorFromSignature signature))
          coreTys coreExprs
      some
        ( targetCore
        , callData
        , SolidCore.Solidity.Source.Expr.word 0 )
  | Expr.callWithOptions (Expr.member target name) options args => do
      if name == "call" || name == "staticcall" ||
          name == "delegatecall" || name == "send" ||
          name == "transfer" then
        none
      else
        some ()
      if Expr.memberCallIsBuiltin? target name then
        none
      else
        some ()
      let targetCore ← Expr.toCore? storageNames target
      let valueCore ← CallOptions.lowLevelCallValueCore? storageNames options
      let (sourceTys, coreTys, coreExprs) ←
        Args.toAbiEncodeSource? storageNames args
      let signature ← externalFunctionSignature? name sourceTys
      let callData :=
        SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
          (SolidCore.Solidity.Source.Expr.word
            (SolidCore.Solidity.Source.ABI.selectorFromSignature signature))
          coreTys coreExprs
      some (targetCore, callData, valueCore)
  | _ => none

def Expr.toContractCreation? (storageNames : List Name) :
    Expr -> Option (Name × CoreExpr × CoreExpr × Option CoreExpr)
  | Expr.newExpr ty args => do
      let contractName ← Ty.contractName? ty
      let (coreTys, coreExprs) ← Args.toAbiEncode? storageNames args
      some
        ( contractName
        , SolidCore.Solidity.Source.Expr.abiEncode coreTys coreExprs
        , SolidCore.Solidity.Source.Expr.word 0
        , none )
  | Expr.callWithOptions (Expr.newExpr ty []) options args => do
      let contractName ← Ty.contractName? ty
      let (value?, salt?) ←
        CallOptions.contractCreationValueSalt? options
      let valueCore ←
        match value? with
        | some value => Expr.toCore? storageNames value
        | none => some (SolidCore.Solidity.Source.Expr.word 0)
      let saltCore? ←
        match salt? with
        | some salt => do
            let saltCore ← Expr.toCore? storageNames salt
            some (some saltCore)
        | none => some none
      let (coreTys, coreExprs) ← Args.toAbiEncode? storageNames args
      some
        ( contractName
        , SolidCore.Solidity.Source.Expr.abiEncode coreTys coreExprs
        , valueCore
        , saltCore? )
  | _ => none

def Ty.toExternalReturnBinding? (namePrefix : String) (index : Nat)
    (ty : Ty) : Option CoreBindingDecl := do
  let coreTy ← Ty.toCore? ty
  some { name := namePrefix ++ toString index, ty := coreTy }

def Tys.toExternalReturnBindings? (namePrefix : String)
    (tys : List Ty) : Option (List CoreBindingDecl) :=
  mapOptionIdx (Ty.toExternalReturnBinding? namePrefix) 0 tys

def CoreBindingDecls.toVarExprs
    (bindings : List CoreBindingDecl) : List CoreExpr :=
  bindings.map (fun binding =>
    SolidCore.Solidity.Source.Expr.var binding.name)

def CoreBindingDecls.assignToVars (names : List Name)
    (bindings : List CoreBindingDecl) : List CoreStmt :=
  (names.zip bindings).map
    (fun pair =>
      SolidCore.Solidity.Source.Stmt.assign
        (SolidCore.Solidity.Source.LValue.var pair.fst)
        (SolidCore.Solidity.Source.Expr.var pair.snd.name))

def Expr.transferCore? (storageNames : List Name)
    (target value : Expr) : Option CoreStmt := do
  let targetCore ← Expr.toCore? storageNames target
  let valueCore ← Expr.toCore? storageNames value
  some
    (SolidCore.Solidity.Source.Stmt.tryExternalCall
      targetCore
      (SolidCore.Solidity.Source.Expr.byteArray [])
      valueCore [] SolidCore.Solidity.Source.Stmt.skip [])

def Expr.externalCallWithReturnsCore? (storageNames : List Name)
    (namePrefix : String) (returnTys : List Ty) (expr : Expr)
    (successBody : List CoreBindingDecl -> CoreStmt) : Option CoreStmt := do
  let (targetCore, calldataCore, valueCore) ←
    Expr.toExternalCall? storageNames expr
  let returnBindings ← Tys.toExternalReturnBindings? namePrefix returnTys
  some
    (SolidCore.Solidity.Source.Stmt.tryExternalCall
      targetCore calldataCore valueCore returnBindings
      (successBody returnBindings) [])

def Expr.externalCallDiscardCore? (storageNames : List Name)
    (expr : Expr) : Option CoreStmt :=
  Expr.externalCallWithReturnsCore?
    storageNames "__ext" [] expr
    (fun _ => SolidCore.Solidity.Source.Stmt.skip)

def Expr.externalCallSingleReturnCore? (storageNames : List Name)
    (expectedTy : Ty) (expr : Expr) (useResult : CoreExpr -> CoreStmt) :
    Option CoreStmt := do
  Expr.externalCallWithReturnsCore?
    storageNames "__ext" [expectedTy] expr
    (fun bindings =>
      match bindings with
      | [binding] =>
          useResult (SolidCore.Solidity.Source.Expr.var binding.name)
      | _ => SolidCore.Solidity.Source.Stmt.skip)

def Expr.externalCallAssignVarsCore? (storageNames : List Name)
    (returnTys : List Ty) (targetNames : List Name) (expr : Expr) :
    Option CoreStmt := do
  if targetNames.length == returnTys.length then
    Expr.externalCallWithReturnsCore?
      storageNames "__ext" returnTys expr
      (fun bindings =>
        SolidCore.Solidity.Source.Stmt.block
          (CoreBindingDecls.assignToVars targetNames bindings))
  else
    none

def Expr.externalCallReturnCore? (storageNames : List Name)
    (returnTys : List Ty) (expr : Expr) : Option CoreStmt :=
  Expr.externalCallWithReturnsCore?
    storageNames "__extret" returnTys expr
    (fun bindings =>
      SolidCore.Solidity.Source.Stmt.returnValues
        (CoreBindingDecls.toVarExprs bindings))

def TupleItems.toAbiDecodeSourceTypes? :
    List TupleItem -> Option (List Ty)
  | [] => some []
  | TupleItem.value (Expr.typeName ty) :: rest => do
      let _ ← Ty.toCore? ty
      let tail ← TupleItems.toAbiDecodeSourceTypes? rest
      some (ty :: tail)
  | _ => none
termination_by items => (sizeOf items, 0)

def Expr.abiDecodeSourceTypes? : Expr -> Option (List Ty)
  | Expr.typeName ty => do
      let _ ← Ty.toCore? ty
      some [ty]
  | Expr.tuple items => TupleItems.toAbiDecodeSourceTypes? items
  | _ => none

def Expr.toAbiDecode? (storageNames : List Name)
    (data typesExpr : Expr) : Option (List CoreTy × CoreExpr) := do
  let sourceTys ← Expr.abiDecodeSourceTypes? typesExpr
  let coreTys ← Ty.listToCore? sourceTys
  let dataCore ← Expr.toCore? storageNames data
  some (coreTys, dataCore)
termination_by (sizeOf data + sizeOf typesExpr + 1, 1)

def Expr.toCoreLValue? (storageNames : List Name) : Expr -> Option CoreLValue
  | Expr.ident name =>
      if stateNameIsStorage name storageNames then
        some (SolidCore.Solidity.Source.LValue.storage name)
      else if stateNameIsImmutable name storageNames then
        some (SolidCore.Solidity.Source.LValue.immutable name)
      else
        some (SolidCore.Solidity.Source.LValue.var name)
  | Expr.index (Expr.ident name) index =>
      if stateNameIsStorage name storageNames then
        do
        let indexCore ← Expr.toCore? storageNames index
        some (SolidCore.Solidity.Source.LValue.storageIndex name indexCore)
      else
        do
        let baseCore ← Expr.toCoreLValue? storageNames (Expr.ident name)
        let indexCore ← Expr.toCore? storageNames index
        some (SolidCore.Solidity.Source.LValue.index baseCore indexCore)
  | Expr.index base index => do
      let baseCore ← Expr.toCoreLValue? storageNames base
      let indexCore ← Expr.toCore? storageNames index
      some (SolidCore.Solidity.Source.LValue.index baseCore indexCore)
  | _ => none
termination_by expr => (sizeOf expr, 0)

def Arg.toCoreExpr? (storageNames : List Name) : Arg -> Option CoreExpr
  | Arg.positional expr => Expr.toCore? storageNames expr
  | Arg.named _ expr => Expr.toCore? storageNames expr

def Args.toCoreExprs? (storageNames : List Name) (args : List Arg) :
    Option (List CoreExpr) :=
  mapOption (Arg.toCoreExpr? storageNames) args

def TupleItems.toCoreExprs? (storageNames : List Name)
    (items : List TupleItem) : Option (List CoreExpr) :=
  match items with
  | [] => some []
  | TupleItem.value expr :: rest => do
      let head ← Expr.toCore? storageNames expr
      let tail ← TupleItems.toCoreExprs? storageNames rest
      some (head :: tail)
  | TupleItem.hole :: _ => none
termination_by (sizeOf items, 1)

def TupleItems.toCoreLValueTargets? (storageNames : List Name) :
    List TupleItem -> Option (List (Option CoreLValue))
  | [] => some []
  | TupleItem.hole :: rest => do
      let tail ← TupleItems.toCoreLValueTargets? storageNames rest
      some (none :: tail)
  | TupleItem.value expr :: rest => do
      let target ← Expr.toCoreLValue? storageNames expr
      let tail ← TupleItems.toCoreLValueTargets? storageNames rest
      some (some target :: tail)
termination_by items => (sizeOf items, 1)

def VarBindings.toCoreTupleDecls? :
    List VarBinding -> Option (List CoreStmt)
  | [] => some []
  | binding :: rest => do
      let tail ← VarBindings.toCoreTupleDecls? rest
      match binding.name, binding.ty with
      | some name, some ty => do
          let coreTy ← Ty.toCore? ty
          some (SolidCore.Solidity.Source.Stmt.varDecl coreTy name none :: tail)
      | some _, none => none
      | none, _ => some tail
termination_by bindings => (sizeOf bindings, 0)

def VarBindings.toCoreTupleTargets? :
    List VarBinding -> Option (List (Option CoreLValue))
  | [] => some []
  | binding :: rest => do
      let tail ← VarBindings.toCoreTupleTargets? rest
      match binding.name with
      | some name =>
          some (some (SolidCore.Solidity.Source.LValue.var name) :: tail)
      | none => some (none :: tail)
termination_by bindings => (sizeOf bindings, 0)

def tupleAssignmentCore? (storageNames : List Name)
    (lhsItems : List TupleItem) (rhs : Expr) : Option CoreStmt := do
  let targets ← TupleItems.toCoreLValueTargets? storageNames lhsItems
  let rhsCore ← Expr.toCore? storageNames rhs
  some (SolidCore.Solidity.Source.Stmt.assignTuple targets rhsCore)

def tupleVarDeclCorePieces? (storageNames : List Name)
    (bindings : List VarBinding) (items : List TupleItem) :
    Option (List CoreStmt × List CoreStmt) := do
  if bindings.length == items.length then
    some ()
  else
    none
  let coreDecls ← VarBindings.toCoreTupleDecls? bindings
  let targets ← VarBindings.toCoreTupleTargets? bindings
  let rhsCore ← Expr.toCore? storageNames (Expr.tuple items)
  some
    ( coreDecls
    , [SolidCore.Solidity.Source.Stmt.assignTuple targets rhsCore] )

def storageArrayPushAssignCore? (storageNames : List Name)
    (name : Name) (rhs : Expr) : Option CoreStmt := do
  if nameIn name storageNames then
    some ()
  else
    none
  let rhsCore ← Expr.toCore? storageNames rhs
  let lastIndex :=
    SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.sub
      (SolidCore.Solidity.Source.Expr.storage name)
      (SolidCore.Solidity.Source.Expr.word 1)
  some
    (SolidCore.Solidity.Source.Stmt.block
      [ SolidCore.Solidity.Source.Stmt.storageArrayPush name none
      , SolidCore.Solidity.Source.Stmt.assign
          (SolidCore.Solidity.Source.LValue.storageIndex name lastIndex)
          rhsCore ])

def Parameter.toCoreTryBinding? (fallbackPrefix : String) (index : Nat)
    (param : Parameter) : Option CoreBindingDecl := do
  let ty ← Ty.toCore? param.ty
  let name := param.name.getD (fallbackPrefix ++ toString index)
  some { name := name, ty := ty }

def Parameters.toCoreTryBindings? (fallbackPrefix : String)
    (params : List Parameter) : Option (List CoreBindingDecl) :=
  mapOptionIdx (Parameter.toCoreTryBinding? fallbackPrefix) 0 params

def Stmt.replaceTopLevelModifierPlaceholder (replacement : Stmt) : Stmt -> Stmt
  | Stmt.block body =>
      Stmt.block
        (body.map (fun stmt =>
          match stmt with
          | Stmt.modifierPlaceholder => replacement
          | other => other))
  | Stmt.modifierPlaceholder => replacement
  | other => other

def Stmt.toCore? (storageNames : List Name) : Stmt -> Option CoreStmt
  | Stmt.empty => some SolidCore.Solidity.Source.Stmt.skip
  | Stmt.block body => do
      let coreBody ← Stmt.listToCore? storageNames body
      some (SolidCore.Solidity.Source.Stmt.block coreBody)
  | Stmt.varDecl bindings@(_ :: _ :: _) (some (Expr.tuple items)) => do
      let (coreDecls, assigns) ←
        tupleVarDeclCorePieces? storageNames bindings items
      some (SolidCore.Solidity.Source.Stmt.block (coreDecls ++ assigns))
  | Stmt.varDecl bindings init =>
      match bindings with
      | [] => some SolidCore.Solidity.Source.Stmt.skip
      | [binding] =>
          match binding.name, binding.ty with
          | some name, some ty =>
              match binding.location, init with
              | some DataLocation.storage, some (Expr.ident target) => do
                  let _ ←
                    match Ty.toCore? ty with
                    | some _ => some ()
                    | none =>
                        match Ty.toCoreStorageLayout? ty with
                        | some _ => some ()
                        | none => none
                  if stateNameIsStorage target storageNames then
                    some
                      (SolidCore.Solidity.Source.Stmt.storageAlias
                        name target)
                  else
                    none
              | some DataLocation.storage, _ => none
              | _, _ => do
                  let coreTy ← Ty.toCore? ty
                  let initCore ←
                    match init with
                    | some expr => do
                        let coreExpr ←
                          match Expr.toCoreFixedBytesLiteralAs? ty expr with
                          | some coreExpr => some coreExpr
                          | none =>
                              if Ty.isFixedBytes ty &&
                                  Expr.isFixedBytesLiteralCandidate expr then
                                none
                              else
                                match Expr.toCoreNumericLiteralAs? ty expr with
                                | some coreExpr => some coreExpr
                                | none =>
                                    if Ty.isIntOrUint ty &&
                                        Expr.isNumberLiteralExpression expr then
                                      none
                                    else
                                      Expr.toCore? storageNames expr
                        some (some coreExpr)
                    | none => some none
                  some (SolidCore.Solidity.Source.Stmt.varDecl coreTy name initCore)
          | _, _ => none
      | _ =>
          match init with
          | some _ => none
          | none => do
              let coreDecls ←
                mapOption
                  (fun binding =>
                    match binding.name, binding.ty with
                    | some name, some ty => do
                        let coreTy ← Ty.toCore? ty
                        some (SolidCore.Solidity.Source.Stmt.varDecl coreTy name none)
                    | _, _ => none)
                  bindings
              some (SolidCore.Solidity.Source.Stmt.block coreDecls)
  | Stmt.expr (Expr.assign (Expr.tuple lhsItems) AssignOp.assign rhs) =>
      tupleAssignmentCore? storageNames lhsItems rhs
  | Stmt.expr
      (Expr.assign
        (Expr.call (Expr.member (Expr.ident name) "push") [])
        AssignOp.assign rhs) =>
      storageArrayPushAssignCore? storageNames name rhs
  | Stmt.expr (Expr.assign lhs AssignOp.assign rhs) => do
      let lhsCore ← Expr.toCoreLValue? storageNames lhs
      let rhsCore ← Expr.toCore? storageNames rhs
      some (SolidCore.Solidity.Source.Stmt.assign lhsCore rhsCore)
  | Stmt.expr (Expr.assign lhs op rhs) => do
      let lhsCore ← Expr.toCoreLValue? storageNames lhs
      let coreOp ← AssignOp.toCoreBinary? op
      let rhsCore ← Expr.toCore? storageNames rhs
      some (SolidCore.Solidity.Source.Stmt.assignOp lhsCore coreOp rhsCore)
  | Stmt.expr (Expr.unary UnaryOp.delete target) => do
      let targetCore ← Expr.toCoreLValue? storageNames target
      some (SolidCore.Solidity.Source.Stmt.deleteValue targetCore)
  | Stmt.expr
      (Expr.call (Expr.member (Expr.ident name) "push") []) =>
      if nameIn name storageNames then
        some (SolidCore.Solidity.Source.Stmt.storageArrayPush name none)
      else
        none
  | Stmt.expr
      (Expr.call (Expr.member (Expr.ident name) "push")
        [Arg.positional value]) =>
      if nameIn name storageNames then
        do
        let valueCore ← Expr.toCore? storageNames value
        some (SolidCore.Solidity.Source.Stmt.storageArrayPush
          name (some valueCore))
      else
        none
  | Stmt.expr
      (Expr.call (Expr.member (Expr.ident name) "pop") []) =>
      if nameIn name storageNames then
        some (SolidCore.Solidity.Source.Stmt.storageArrayPop name)
      else
        none
  | Stmt.expr
      (Expr.call (Expr.member target "transfer") [Arg.positional value]) =>
      Expr.transferCore? storageNames target value
  | Stmt.expr
      (Expr.call (Expr.ident "selfdestruct") [Arg.positional recipient]) => do
      let recipientCore ← Expr.toCore? storageNames recipient
      some (SolidCore.Solidity.Source.Stmt.selfdestruct recipientCore)
  | Stmt.expr (Expr.call (Expr.ident "assert") [Arg.positional cond]) => do
      let condCore ← Expr.toCore? storageNames cond
      some (SolidCore.Solidity.Source.Stmt.assertStmt condCore)
  | Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional cond]) => do
      let condCore ← Expr.toCore? storageNames cond
      some (SolidCore.Solidity.Source.Stmt.requireStmt condCore none)
  | Stmt.expr
      (Expr.call (Expr.ident "require")
        [Arg.positional cond, Arg.positional (Expr.literal (Literal.string reason))]) => do
      let condCore ← Expr.toCore? storageNames cond
      some (SolidCore.Solidity.Source.Stmt.requireStmt condCore (some reason))
  | Stmt.expr
      (Expr.call (Expr.ident "require")
        [Arg.positional cond, Arg.positional (Expr.call (Expr.ident name) args)]) => do
      let condCore ← Expr.toCore? storageNames cond
      let coreArgs ← Args.toCoreExprs? storageNames args
      some (SolidCore.Solidity.Source.Stmt.requireCustom
        condCore name coreArgs)
  | Stmt.expr
      (Expr.call (Expr.ident "require")
        [Arg.positional cond, Arg.positional reason]) => do
      let condCore ← Expr.toCore? storageNames cond
      let reasonCore ← Expr.toCore? storageNames reason
      some (SolidCore.Solidity.Source.Stmt.requireErrorExpr
        condCore reasonCore)
  | Stmt.expr expr => do
      let coreExpr ← Expr.toCore? storageNames expr
      some (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
  | Stmt.ifElse cond thenBranch elseBranch => do
      let condCore ← Expr.toCore? storageNames cond
      let thenCore ← Stmt.toCore? storageNames thenBranch
      let elseCore ←
        match elseBranch with
        | some stmt => Stmt.toCore? storageNames stmt
        | none => some SolidCore.Solidity.Source.Stmt.skip
      some (SolidCore.Solidity.Source.Stmt.ifElse condCore thenCore elseCore)
  | Stmt.whileLoop cond body => do
      let condCore ← Expr.toCore? storageNames cond
      let bodyCore ← Stmt.toCore? storageNames body
      some (SolidCore.Solidity.Source.Stmt.whileLoop condCore bodyCore)
  | Stmt.doWhile body cond => do
      let bodyCore ← Stmt.toCore? storageNames body
      let condCore ← Expr.toCore? storageNames cond
      some (SolidCore.Solidity.Source.Stmt.doWhile bodyCore condCore)
  | Stmt.forLoop init cond post body => do
      let initCore ←
        match init with
        | some stmt => Stmt.toCore? storageNames stmt
        | none => some SolidCore.Solidity.Source.Stmt.skip
      let condCore ←
        match cond with
        | some expr => Expr.toCore? storageNames expr
        | none => some (SolidCore.Solidity.Source.Expr.word 1)
      let postCore ←
        match post with
        | some expr => Stmt.toCore? storageNames (Stmt.expr expr)
        | none => some SolidCore.Solidity.Source.Stmt.skip
      let bodyCore ← Stmt.toCore? storageNames body
      some (SolidCore.Solidity.Source.Stmt.forLoop initCore condCore postCore bodyCore)
  | Stmt.tryCatch expr clauses => do
      match Expr.toExternalCall? storageNames expr with
      | some (targetCore, calldataCore, valueCore) => do
          let catchCore ← CatchClause.listToCore? storageNames clauses
          some
            (SolidCore.Solidity.Source.Stmt.tryExternalCall
              targetCore calldataCore valueCore []
              SolidCore.Solidity.Source.Stmt.skip catchCore)
      | none => do
          let (contractName, argsCore, valueCore, saltCore?) ←
            Expr.toContractCreation? storageNames expr
          let catchCore ← CatchClause.listToCore? storageNames clauses
          some
            (SolidCore.Solidity.Source.Stmt.tryContractCreate
              contractName argsCore valueCore saltCore? []
              SolidCore.Solidity.Source.Stmt.skip catchCore)
  | Stmt.tryCatchReturns expr returns success clauses => do
      let returnBindings ← Parameters.toCoreTryBindings? "_try" returns
      match Expr.toExternalCall? storageNames expr with
      | some (targetCore, calldataCore, valueCore) => do
          let successCore ← Stmt.toCore? storageNames success
          let catchCore ← CatchClause.listToCore? storageNames clauses
          some
            (SolidCore.Solidity.Source.Stmt.tryExternalCall
              targetCore calldataCore valueCore returnBindings successCore
              catchCore)
      | none => do
          let (contractName, argsCore, valueCore, saltCore?) ←
            Expr.toContractCreation? storageNames expr
          let successCore ← Stmt.toCore? storageNames success
          let catchCore ← CatchClause.listToCore? storageNames clauses
          some
            (SolidCore.Solidity.Source.Stmt.tryContractCreate
              contractName argsCore valueCore saltCore? returnBindings
              successCore catchCore)
  | Stmt.emitEvent (Expr.call (Expr.ident name) args) => do
      let coreArgs ← Args.toCoreExprs? storageNames args
      some (SolidCore.Solidity.Source.Stmt.emitEvent name coreArgs)
  | Stmt.revertCall (Expr.call (Expr.ident "revert") []) =>
      some (SolidCore.Solidity.Source.Stmt.revertError none)
  | Stmt.revertCall
      (Expr.call (Expr.ident "revert")
        [Arg.positional (Expr.literal (Literal.string reason))]) =>
      some (SolidCore.Solidity.Source.Stmt.revertError (some reason))
  | Stmt.revertCall
      (Expr.call (Expr.ident "revert") [Arg.positional reason]) => do
      let reasonCore ← Expr.toCore? storageNames reason
      some (SolidCore.Solidity.Source.Stmt.revertErrorExpr reasonCore)
  | Stmt.revertCall (Expr.call (Expr.ident name) args) => do
      let coreArgs ← Args.toCoreExprs? storageNames args
      some (SolidCore.Solidity.Source.Stmt.revert name coreArgs)
  | Stmt.returnValues none => some (SolidCore.Solidity.Source.Stmt.returnValues [])
  | Stmt.returnValues
      (some
        (Expr.call (Expr.member (Expr.ident "abi") "decode")
          [Arg.positional data, Arg.positional typesExpr])) => do
      let (tys, dataCore) ← Expr.toAbiDecode? storageNames data typesExpr
      some
        (SolidCore.Solidity.Source.Stmt.returnValues
          (abiDecodeReturnExprs tys dataCore))
  | Stmt.returnValues (some (Expr.tuple items)) => do
      let coreExprs ← TupleItems.toCoreExprs? storageNames items
      some (SolidCore.Solidity.Source.Stmt.returnValues coreExprs)
  | Stmt.returnValues (some expr) => do
      let coreExpr ← Expr.toCore? storageNames expr
      some (SolidCore.Solidity.Source.Stmt.returnValues [coreExpr])
  | Stmt.break => some SolidCore.Solidity.Source.Stmt.break
  | Stmt.continue => some SolidCore.Solidity.Source.Stmt.continue
  | Stmt.unchecked body => do
      let coreBody ← Stmt.toCore? storageNames body
      some (SolidCore.Solidity.Source.Stmt.unchecked coreBody)
  | _ => none
termination_by stmt => (sizeOf stmt, 0)

def Stmt.listToCore? (storageNames : List Name) :
    List Stmt -> Option (List CoreStmt)
  | [] => some []
  | Stmt.varDecl bindings@(_ :: _ :: _) (some (Expr.tuple items)) :: rest => do
      let (coreDecls, assigns) ←
        tupleVarDeclCorePieces? storageNames bindings items
      let tail ← Stmt.listToCore? storageNames rest
      some (coreDecls ++ assigns ++ tail)
  | stmt :: rest => do
      let head ← Stmt.toCore? storageNames stmt
      let tail ← Stmt.listToCore? storageNames rest
      some (head :: tail)
termination_by stmts => (sizeOf stmts, 1)

def CatchClause.toCore? (storageNames : List Name)
    (clause : CatchClause) : Option CoreTryCatchClause :=
  match clause with
  | CatchClause.clause name params body => do
      let bindings ← Parameters.toCoreTryBindings? "_catch" params
      let bodyCore ← Stmt.toCore? storageNames body
      some (SolidCore.Solidity.Source.TryCatchClause.clause
        name bindings bodyCore)
termination_by (sizeOf clause, 0)

def CatchClause.listToCore? (storageNames : List Name) :
    List CatchClause -> Option (List CoreTryCatchClause)
  | [] => some []
  | clause :: rest => do
      let head ← CatchClause.toCore? storageNames clause
      let tail ← CatchClause.listToCore? storageNames rest
      some (head :: tail)
termination_by clauses => (sizeOf clauses, 0)

end

def Expr.abiTyWithEnv? (env : TypeEnv) : Expr -> Option Ty
  | Expr.ident name => TypeEnv.lookup? env name
  | expr =>
      match Expr.abiTy? [] expr with
      | some ty => some ty
      | none =>
          match expr with
          | Expr.unary UnaryOp.bitNot inner =>
              Expr.abiTyWithEnv? env inner
          | Expr.unary UnaryOp.neg inner =>
              Expr.abiTyWithEnv? env inner
          | Expr.binary op lhs _ =>
              match op with
              | BinaryOp.lt | BinaryOp.gt | BinaryOp.le | BinaryOp.ge
              | BinaryOp.eq | BinaryOp.ne
              | BinaryOp.boolAnd | BinaryOp.boolOr => some Ty.bool
              | _ => Expr.abiTyWithEnv? env lhs
          | Expr.ternary _ thenExpr _ =>
              Expr.abiTyWithEnv? env thenExpr
          | Expr.member base "balance" => do
              let _ ← Expr.abiTyWithEnv? env base
              some (Ty.uint 256)
          | Expr.member base "code" => do
              let _ ← Expr.abiTyWithEnv? env base
              some Ty.bytes
          | Expr.member base "codehash" => do
              let _ ← Expr.abiTyWithEnv? env base
              some (Ty.bytesN 32)
          | Expr.member base "length" => do
              let _ ← Expr.abiTyWithEnv? env base
              some (Ty.uint 256)
          | _ => none

def Expr.annotateAbiFuel : Nat -> TypeEnv -> Expr -> Expr
  | 0, _, expr => expr
  | fuel + 1, env, expr =>
      let annotate := Expr.annotateAbiFuel fuel env
      let annotateArg : Arg -> Arg
        | Arg.positional argExpr => Arg.positional (annotate argExpr)
        | Arg.named name argExpr => Arg.named name (annotate argExpr)
      let annotateAbiArg : Arg -> Arg
        | Arg.positional argExpr =>
            let annotated := annotate argExpr
            let encoded :=
              match Expr.abiTy? [] annotated with
              | some _ => annotated
              | none =>
                  match Expr.abiTyWithEnv? env annotated with
                  | some ty =>
                      Expr.call (Expr.typeName ty) [Arg.positional annotated]
                  | none => annotated
            Arg.positional encoded
        | Arg.named name argExpr =>
            let annotated := annotate argExpr
            let encoded :=
              match Expr.abiTy? [] annotated with
              | some _ => annotated
              | none =>
                  match Expr.abiTyWithEnv? env annotated with
                  | some ty =>
                      Expr.call (Expr.typeName ty) [Arg.positional annotated]
                  | none => annotated
            Arg.named name encoded
      let annotateOption : CallOption -> CallOption
        | CallOption.named name optionExpr =>
            CallOption.named name (annotate optionExpr)
      let annotateTupleItem : TupleItem -> TupleItem
        | TupleItem.hole => TupleItem.hole
        | TupleItem.value itemExpr => TupleItem.value (annotate itemExpr)
      let annotateAbiTupleItem : TupleItem -> TupleItem
        | TupleItem.hole => TupleItem.hole
        | TupleItem.value itemExpr =>
            let annotated := annotate itemExpr
            let encoded :=
              match Expr.abiTy? [] annotated with
              | some _ => annotated
              | none =>
                  match Expr.abiTyWithEnv? env annotated with
                  | some ty =>
                      Expr.call (Expr.typeName ty) [Arg.positional annotated]
                  | none => annotated
            TupleItem.value encoded
      match expr with
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (annotate base) member
      | Expr.index base index => Expr.index (annotate base) (annotate index)
      | Expr.slice base start stop =>
          Expr.slice (annotate base) (start.map annotate) (stop.map annotate)
      | Expr.call (Expr.member (Expr.ident "abi") "encode") args =>
          Expr.call (Expr.member (Expr.ident "abi") "encode")
            (args.map annotateAbiArg)
      | Expr.call (Expr.member (Expr.ident "abi") "encodePacked") args =>
          Expr.call (Expr.member (Expr.ident "abi") "encodePacked")
            (args.map annotateAbiArg)
      | Expr.call (Expr.member (Expr.ident "abi") "encodeWithSelector") args =>
          Expr.call (Expr.member (Expr.ident "abi") "encodeWithSelector")
            (args.map annotateAbiArg)
      | Expr.call (Expr.member (Expr.ident "abi") "encodeWithSignature") args =>
          match args with
          | [] =>
              Expr.call
                (Expr.member (Expr.ident "abi") "encodeWithSignature") []
          | head :: rest =>
              Expr.call
                (Expr.member (Expr.ident "abi") "encodeWithSignature")
                (annotateArg head :: rest.map annotateAbiArg)
      | Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
          [Arg.positional functionPointer, Arg.positional (Expr.tuple items)] =>
          Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
            [ Arg.positional (annotate functionPointer)
            , Arg.positional
                (Expr.tuple (items.map annotateAbiTupleItem)) ]
      | Expr.call (Expr.member (Expr.ident "abi") "decode")
          [Arg.positional data, typesExpr] =>
          Expr.call (Expr.member (Expr.ident "abi") "decode")
            [Arg.positional (annotate data), typesExpr]
      | Expr.call (Expr.member target name) args =>
          Expr.call (Expr.member (annotate target) name)
            (args.map annotateAbiArg)
      | Expr.callWithOptions (Expr.member target name) options args =>
          Expr.callWithOptions (Expr.member (annotate target) name)
            (options.map annotateOption) (args.map annotateAbiArg)
      | Expr.call (Expr.typeName ty) [Arg.positional argExpr] =>
          let annotated := annotate argExpr
          let encoded :=
            match Expr.abiTy? [] annotated with
            | some _ => annotated
            | none =>
                match Expr.abiTyWithEnv? env annotated with
                | some sourceTy =>
                    Expr.call (Expr.typeName sourceTy)
                      [Arg.positional annotated]
                | none => annotated
          Expr.call (Expr.typeName ty) [Arg.positional encoded]
      | Expr.call fn args =>
          Expr.call (annotate fn) (args.map annotateArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (annotate fn)
            (options.map annotateOption) (args.map annotateArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map annotateArg)
      | Expr.tuple items => Expr.tuple (items.map annotateTupleItem)
      | Expr.array exprs => Expr.array (exprs.map annotate)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (annotate inner)
      | Expr.unary op inner => Expr.unary op (annotate inner)
      | Expr.binary op lhs rhs =>
          Expr.binary op (annotate lhs) (annotate rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (annotate cond) (annotate thenExpr)
            (annotate elseExpr)
      | Expr.assign lhs op rhs => Expr.assign lhs op (annotate rhs)
      | Expr.payableConversion inner => Expr.payableConversion (annotate inner)

def defaultAnnotateAbiFuel : Nat := 1024

def Expr.annotateAbi (env : TypeEnv) (expr : Expr) : Expr :=
  Expr.annotateAbiFuel defaultAnnotateAbiFuel env expr

def Stmt.annotateAbiInSeqFuel :
    Nat -> TypeEnv -> Stmt -> Stmt × TypeEnv
  | 0, env, stmt => (stmt, env)
  | fuel + 1, env, stmt =>
      let annotateExpr := Expr.annotateAbiFuel fuel env
      let annotateStmt (child : Stmt) :=
        (Stmt.annotateAbiInSeqFuel fuel env child).fst
      let annotateSeq (env : TypeEnv) (body : List Stmt) :
          List Stmt × TypeEnv :=
        let step (acc : List Stmt × TypeEnv) (head : Stmt) :
            List Stmt × TypeEnv :=
          let (done, env) := acc
          let (head', env') := Stmt.annotateAbiInSeqFuel fuel env head
          (head' :: done, env')
        let (revBody, finalEnv) :=
          body.foldl step (([] : List Stmt), env)
        (revBody.reverse, finalEnv)
      let annotateClause : CatchClause -> CatchClause
        | CatchClause.clause name params body =>
            let clauseEnv := Parameters.extendTypeEnv "_catch" env params
            CatchClause.clause name params
              ((Stmt.annotateAbiInSeqFuel fuel clauseEnv body).fst)
      match stmt with
      | Stmt.empty => (Stmt.empty, env)
      | Stmt.block body =>
          let (body', _) := annotateSeq env body
          (Stmt.block body', env)
      | Stmt.varDecl bindings init =>
          let init' := init.map annotateExpr
          let env' := VarBindings.extendTypeEnv env bindings
          (Stmt.varDecl bindings init', env')
      | Stmt.expr expr => (Stmt.expr (annotateExpr expr), env)
      | Stmt.ifElse cond thenBranch elseBranch =>
          let thenBranch' := annotateStmt thenBranch
          let elseBranch' := elseBranch.map annotateStmt
          (Stmt.ifElse (annotateExpr cond) thenBranch' elseBranch', env)
      | Stmt.whileLoop cond body =>
          (Stmt.whileLoop (annotateExpr cond) (annotateStmt body), env)
      | Stmt.doWhile body cond =>
          (Stmt.doWhile (annotateStmt body) (annotateExpr cond), env)
      | Stmt.forLoop init cond post body =>
          let (init', loopEnv) :=
            match init with
            | some initStmt =>
                let (stmt', env') :=
                  Stmt.annotateAbiInSeqFuel fuel env initStmt
                (some stmt', env')
            | none => (none, env)
          let annotateLoopExpr := Expr.annotateAbiFuel fuel loopEnv
          let body' := (Stmt.annotateAbiInSeqFuel fuel loopEnv body).fst
          (Stmt.forLoop init' (cond.map annotateLoopExpr)
            (post.map annotateLoopExpr) body', env)
      | Stmt.tryCatch expr clauses =>
          (Stmt.tryCatch (annotateExpr expr) (clauses.map annotateClause), env)
      | Stmt.tryCatchReturns expr returns success clauses =>
          let successEnv := Parameters.extendTypeEnv "_try" env returns
          let success' := (Stmt.annotateAbiInSeqFuel fuel successEnv success).fst
          (Stmt.tryCatchReturns (annotateExpr expr) returns success'
            (clauses.map annotateClause), env)
      | Stmt.emitEvent expr => (Stmt.emitEvent (annotateExpr expr), env)
      | Stmt.revertCall expr => (Stmt.revertCall (annotateExpr expr), env)
      | Stmt.returnValues expr? =>
          (Stmt.returnValues (expr?.map annotateExpr), env)
      | Stmt.break => (Stmt.break, env)
      | Stmt.continue => (Stmt.continue, env)
      | Stmt.unchecked body => (Stmt.unchecked (annotateStmt body), env)
      | Stmt.inlineAssembly code => (Stmt.inlineAssembly code, env)
      | Stmt.modifierPlaceholder => (Stmt.modifierPlaceholder, env)

def Stmt.annotateAbiFuel (fuel : Nat) (env : TypeEnv) (stmt : Stmt) :
    Stmt :=
  (Stmt.annotateAbiInSeqFuel fuel env stmt).fst

def Stmt.annotateAbi (env : TypeEnv) (stmt : Stmt) : Stmt :=
  Stmt.annotateAbiFuel defaultAnnotateAbiFuel env stmt

mutual

def Stmt.toCoreReplacingModifierPlaceholder?
    (storageNames returnNames : List Name) (replacement : CoreStmt) :
    Stmt -> Option CoreStmt
  | Stmt.modifierPlaceholder =>
      some (SolidCore.Solidity.Source.Stmt.captureReturn
        returnNames replacement)
  | Stmt.block body => do
      let coreBody ←
        Stmt.listToCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement body
      some (SolidCore.Solidity.Source.Stmt.block coreBody)
  | Stmt.ifElse cond thenBranch elseBranch => do
      let condCore ← Expr.toCore? storageNames cond
      let thenCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement thenBranch
      let elseCore ←
        match elseBranch with
        | some stmt =>
            Stmt.toCoreReplacingModifierPlaceholder?
              storageNames returnNames replacement stmt
        | none => some SolidCore.Solidity.Source.Stmt.skip
      some (SolidCore.Solidity.Source.Stmt.ifElse
        condCore thenCore elseCore)
  | Stmt.whileLoop cond body => do
      let condCore ← Expr.toCore? storageNames cond
      let bodyCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement body
      some (SolidCore.Solidity.Source.Stmt.whileLoop condCore bodyCore)
  | Stmt.doWhile body cond => do
      let bodyCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement body
      let condCore ← Expr.toCore? storageNames cond
      some (SolidCore.Solidity.Source.Stmt.doWhile bodyCore condCore)
  | Stmt.forLoop init cond post body => do
      let initCore ←
        match init with
        | some stmt =>
            Stmt.toCoreReplacingModifierPlaceholder?
              storageNames returnNames replacement stmt
        | none => some SolidCore.Solidity.Source.Stmt.skip
      let condCore ←
        match cond with
        | some expr => Expr.toCore? storageNames expr
        | none => some (SolidCore.Solidity.Source.Expr.word 1)
      let postCore ←
        match post with
        | some expr => Stmt.toCore? storageNames (Stmt.expr expr)
        | none => some SolidCore.Solidity.Source.Stmt.skip
      let bodyCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement body
      some (SolidCore.Solidity.Source.Stmt.forLoop
        initCore condCore postCore bodyCore)
  | Stmt.tryCatch expr clauses => do
      let catchCore ←
        CatchClause.listToCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement clauses
      match Expr.toExternalCall? storageNames expr with
      | some (targetCore, calldataCore, valueCore) =>
          some
            (SolidCore.Solidity.Source.Stmt.tryExternalCall
              targetCore calldataCore valueCore []
              SolidCore.Solidity.Source.Stmt.skip catchCore)
      | none => do
          let (contractName, argsCore, valueCore, saltCore?) ←
            Expr.toContractCreation? storageNames expr
          some
            (SolidCore.Solidity.Source.Stmt.tryContractCreate
              contractName argsCore valueCore saltCore? []
              SolidCore.Solidity.Source.Stmt.skip catchCore)
  | Stmt.tryCatchReturns expr returns success clauses => do
      let returnBindings ← Parameters.toCoreTryBindings? "_try" returns
      let successCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement success
      let catchCore ←
        CatchClause.listToCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement clauses
      match Expr.toExternalCall? storageNames expr with
      | some (targetCore, calldataCore, valueCore) =>
          some
            (SolidCore.Solidity.Source.Stmt.tryExternalCall
              targetCore calldataCore valueCore returnBindings successCore
              catchCore)
      | none => do
          let (contractName, argsCore, valueCore, saltCore?) ←
            Expr.toContractCreation? storageNames expr
          some
            (SolidCore.Solidity.Source.Stmt.tryContractCreate
              contractName argsCore valueCore saltCore? returnBindings
              successCore catchCore)
  | Stmt.unchecked body => do
      let bodyCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement body
      some (SolidCore.Solidity.Source.Stmt.unchecked bodyCore)
  | other => Stmt.toCore? storageNames other
termination_by stmt => (sizeOf stmt, 0)

def CatchClause.toCoreReplacingModifierPlaceholder?
    (storageNames returnNames : List Name) (replacement : CoreStmt)
    (clause : CatchClause) : Option CoreTryCatchClause :=
  match clause with
  | CatchClause.clause name params body => do
      let bindings ← Parameters.toCoreTryBindings? "_catch" params
      let bodyCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement body
      some
        (SolidCore.Solidity.Source.TryCatchClause.clause
          name bindings bodyCore)
termination_by (sizeOf clause, 1)

def CatchClause.listToCoreReplacingModifierPlaceholder?
    (storageNames returnNames : List Name) (replacement : CoreStmt)
    (clauses : List CatchClause) : Option (List CoreTryCatchClause) :=
  match clauses with
  | [] => some []
  | clause :: rest => do
      let head ←
        CatchClause.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement clause
      let tail ←
        CatchClause.listToCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement rest
      some (head :: tail)
termination_by (sizeOf clauses, 2)

def Stmt.listToCoreReplacingModifierPlaceholder?
    (storageNames returnNames : List Name) (replacement : CoreStmt)
    (stmts : List Stmt) : Option (List CoreStmt) :=
  match stmts with
  | [] => some []
  | stmt :: rest => do
      let head ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement stmt
      let tail ←
        Stmt.listToCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement rest
      some (head :: tail)
termination_by (sizeOf stmts, 1)

end

def Parameter.toCoreBinding? (fallbackPrefix : String) (index : Nat)
    (param : Parameter) : Option CoreBindingDecl := do
  let ty ← Ty.toCore? param.ty
  let name := param.name.getD (fallbackPrefix ++ toString index)
  some { name := name, ty := ty }

def Parameters.toCoreBindings? (fallbackPrefix : String)
    (params : List Parameter) : Option (List CoreBindingDecl) :=
  mapOptionIdx (Parameter.toCoreBinding? fallbackPrefix) 0 params

def Parameter.toVarDeclWithArg (fallbackPrefix : String) (index : Nat)
    (param : Parameter) (arg : Expr) : Stmt :=
  Stmt.varDecl
    [{ name := some (param.name.getD (fallbackPrefix ++ toString index))
       ty := some param.ty
       location := param.location }]
    (some arg)

def Parameters.toVarDeclsWithArgs? (fallbackPrefix : String)
    (params : List Parameter) (args : List Expr) : Option (List Stmt) :=
  if params.length == args.length then
    some
      (mapIdx
        (fun index pair =>
          Parameter.toVarDeclWithArg
            fallbackPrefix index pair.fst pair.snd)
        0 (params.zip args))
  else
    none

def Ty.storageReferenceSupported? (ty : Ty) : Option Unit :=
  match Ty.toCore? ty with
  | some _ => some ()
  | none =>
      match Ty.toCoreStorageLayout? ty with
      | some _ => some ()
      | none => none

def Parameter.toStorageAwareCoreArgDecl? (storageRefEnv : StorageRefEnv)
    (storageNames : List Name) (fallbackPrefix : String) (index : Nat)
    (param : Parameter) (arg : Expr) : Option CoreStmt := do
  let name := param.name.getD (fallbackPrefix ++ toString index)
  match param.location with
  | some DataLocation.storage =>
      let _ ← Ty.storageReferenceSupported? param.ty
      match arg with
      | Expr.ident target =>
          if stateNameIsStorage target storageNames then
            some (SolidCore.Solidity.Source.Stmt.storageAlias name target)
          else if StorageRefEnv.isStorageRef storageRefEnv target then
            some (SolidCore.Solidity.Source.Stmt.storageAliasFrom name target)
          else
            none
      | _ => none
  | _ =>
      Stmt.toCore? storageNames
        (Parameter.toVarDeclWithArg fallbackPrefix index param arg)

def Parameters.toStorageAwareCoreArgDecls? (storageRefEnv : StorageRefEnv)
    (storageNames : List Name) (fallbackPrefix : String)
    (params : List Parameter) (args : List Expr) :
    Option (List CoreStmt) :=
  if params.length == args.length then
    mapOptionIdx
      (fun index pair =>
        Parameter.toStorageAwareCoreArgDecl?
          storageRefEnv storageNames fallbackPrefix index pair.fst pair.snd)
      0 (params.zip args)
  else
    none

def Parameter.toDefaultVarDecl (fallbackPrefix : String) (index : Nat)
    (param : Parameter) : Stmt :=
  Stmt.varDecl
    [{ name := some (param.name.getD (fallbackPrefix ++ toString index))
       ty := some param.ty
       location := param.location }]
    none

def Parameters.toDefaultVarDecls (fallbackPrefix : String)
    (params : List Parameter) : List Stmt :=
  mapIdx (Parameter.toDefaultVarDecl fallbackPrefix) 0 params

def VarBinding.toCoreDecl? (binding : VarBinding) : Option CoreStmt := do
  let name ← binding.name
  let ty ← binding.ty
  let coreTy ← Ty.toCore? ty
  some (SolidCore.Solidity.Source.Stmt.varDecl coreTy name none)

def VarBindings.toCoreDecls? :
    List VarBinding -> Option (List CoreStmt) :=
  mapOption VarBinding.toCoreDecl?

def VarBindings.names? : List VarBinding -> Option (List Name)
  | [] => some []
  | binding :: rest => do
      let name ← binding.name
      let tail ← VarBindings.names? rest
      some (name :: tail)

def VarBindings.sourceTys? : List VarBinding -> Option (List Ty)
  | [] => some []
  | binding :: rest => do
      let ty ← binding.ty
      let tail ← VarBindings.sourceTys? rest
      some (ty :: tail)

def Parameters.abiCanonicalTypes? (params : List Parameter) :
    Option (List String) :=
  mapOption (fun param => Ty.abiCanonical? param.ty) params

def FunctionDecl.abiSignature? (decl : FunctionDecl) : Option String := do
  match decl.kind with
  | FunctionKind.function => some ()
  | _ => none
  let name ← decl.name
  let paramTypes ← Parameters.abiCanonicalTypes? decl.params
  some (name ++ "(" ++ joinStringsWith "," paramTypes ++ ")")

def FunctionDecl.abiSelector? (decl : FunctionDecl) : Option Word := do
  let signature ← FunctionDecl.abiSignature? decl
  some (SolidCore.Solidity.Source.ABI.selectorFromSignature signature)

def FunctionDecl.selectorEntry? (decl : FunctionDecl) :
    Option (Name × Word) := do
  let name ← decl.name
  let selector ← FunctionDecl.abiSelector? decl
  some (name, selector)

def ErrorDecl.abiSignature? (decl : ErrorDecl) : Option String := do
  let paramTypes ← Parameters.abiCanonicalTypes? decl.params
  some (decl.name ++ "(" ++ joinStringsWith "," paramTypes ++ ")")

def ErrorDecl.abiSelector? (decl : ErrorDecl) : Option Word := do
  let signature ← ErrorDecl.abiSignature? decl
  some (SolidCore.Solidity.Source.ABI.selectorFromSignature signature)

def ErrorDecl.selectorEntry? (decl : ErrorDecl) :
    Option (Name × Word) := do
  let selector ← ErrorDecl.abiSelector? decl
  some (decl.name, selector)

def StateVarDecl.publicGetterSignature? (decl : StateVarDecl) :
    Option String :=
  match decl.visibility with
  | some Visibility.public_ =>
      match decl.ty with
      | Ty.mapping keyTy _ => do
          let keyCanonical ← Ty.abiCanonical? keyTy
          some (decl.name ++ "(" ++ keyCanonical ++ ")")
      | Ty.array _ _ => some (decl.name ++ "(uint256)")
      | _ => some (decl.name ++ "()")
  | _ => none

def StateVarDecl.selectorEntry? (decl : StateVarDecl) :
    Option (Name × Word) := do
  let signature ← StateVarDecl.publicGetterSignature? decl
  some
    ( decl.name
    , SolidCore.Solidity.Source.ABI.selectorFromSignature signature )

abbrev SelectorEnv := List (Name × Word)

def SelectorEnv.lookupCompatibleLoop? (query : Name) :
    Option Word -> SelectorEnv -> Option (Option Word)
  | seen?, [] => some seen?
  | seen?, (name, selector) :: rest =>
      if name == query then
        match seen? with
        | none => SelectorEnv.lookupCompatibleLoop? query (some selector) rest
        | some seen =>
            if SolidCore.Solidity.Source.wordEq seen selector then
              SelectorEnv.lookupCompatibleLoop? query seen? rest
            else
              none
      else
        SelectorEnv.lookupCompatibleLoop? query seen? rest

def SelectorEnv.lookup? (env : SelectorEnv) (query : Name) :
    Option Word := do
  let result ← SelectorEnv.lookupCompatibleLoop? query none env
  result

def FunctionDecls.selectorEntries (decls : List FunctionDecl) :
    SelectorEnv :=
  decls.filterMap FunctionDecl.selectorEntry?

def ErrorDecls.selectorEntries (decls : List ErrorDecl) :
    SelectorEnv :=
  decls.filterMap ErrorDecl.selectorEntry?

def StateVarDecls.selectorEntries (decls : List StateVarDecl) :
    SelectorEnv :=
  decls.filterMap StateVarDecl.selectorEntry?

def selectorLiteralExpr (selector : Word) : Expr :=
  Expr.call (Expr.typeName (Ty.bytesN 4))
    [Arg.positional (Expr.literal (Literal.number (toString selector)))]

def FunctionDecls.interfaceId? : List FunctionDecl -> Option Word
  | [] => some 0
  | decl :: rest => do
      let selector ← FunctionDecl.abiSelector? decl
      let tail ← FunctionDecls.interfaceId? rest
      some (SharedSemantics.xorWord selector tail)

abbrev InterfaceIdEnv := List (Name × Word)

def InterfaceIdEnv.lookup? : InterfaceIdEnv -> Name -> Option Word
  | [], _ => none
  | (name, interfaceId) :: rest, query =>
      if name == query then
        some interfaceId
      else
        InterfaceIdEnv.lookup? rest query

def interfaceIdLiteralExpr (interfaceId : Word) : Expr :=
  Expr.call (Expr.typeName (Ty.bytesN 4))
    [Arg.positional (Expr.literal (Literal.number (toString interfaceId)))]

mutual

def Expr.resolveInterfaceIdsFuel : Nat -> InterfaceIdEnv -> Expr -> Expr
  | 0, _, expr => expr
  | fuel + 1, env, expr =>
      let resolve := Expr.resolveInterfaceIdsFuel fuel env
      let resolveArg := Arg.resolveInterfaceIdsFuel fuel env
      let resolveOption := CallOption.resolveInterfaceIdsFuel fuel env
      let resolveTupleItem := TupleItem.resolveInterfaceIdsFuel fuel env
      match expr with
      | Expr.member (Expr.typeName (Ty.user path)) "interfaceId" =>
          match pathLast? path with
          | some name =>
              match InterfaceIdEnv.lookup? env name with
              | some interfaceId => interfaceIdLiteralExpr interfaceId
              | none => expr
          | none => expr
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (resolve base) member
      | Expr.index base index => Expr.index (resolve base) (resolve index)
      | Expr.slice base start stop =>
          Expr.slice (resolve base) (start.map resolve) (stop.map resolve)
      | Expr.call fn args =>
          Expr.call (resolve fn) (args.map resolveArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (resolve fn)
            (options.map resolveOption) (args.map resolveArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map resolveArg)
      | Expr.tuple items => Expr.tuple (items.map resolveTupleItem)
      | Expr.array exprs => Expr.array (exprs.map resolve)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (resolve inner)
      | Expr.unary op inner => Expr.unary op (resolve inner)
      | Expr.binary op lhs rhs =>
          Expr.binary op (resolve lhs) (resolve rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (resolve cond) (resolve thenExpr) (resolve elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (resolve lhs) op (resolve rhs)
      | Expr.payableConversion inner => Expr.payableConversion (resolve inner)

def Arg.resolveInterfaceIdsFuel :
    Nat -> InterfaceIdEnv -> Arg -> Arg
  | 0, _, arg => arg
  | fuel + 1, env, arg =>
      let resolve := Expr.resolveInterfaceIdsFuel fuel env
      match arg with
      | Arg.positional expr => Arg.positional (resolve expr)
      | Arg.named name expr => Arg.named name (resolve expr)

def CallOption.resolveInterfaceIdsFuel :
    Nat -> InterfaceIdEnv -> CallOption -> CallOption
  | 0, _, option => option
  | fuel + 1, env, option =>
      let resolve := Expr.resolveInterfaceIdsFuel fuel env
      match option with
      | CallOption.named name expr => CallOption.named name (resolve expr)

def TupleItem.resolveInterfaceIdsFuel :
    Nat -> InterfaceIdEnv -> TupleItem -> TupleItem
  | 0, _, item => item
  | fuel + 1, env, item =>
      let resolve := Expr.resolveInterfaceIdsFuel fuel env
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (resolve expr)

end

def defaultResolveInterfaceIdsFuel : Nat := 1024

def Expr.resolveInterfaceIds (env : InterfaceIdEnv) (expr : Expr) : Expr :=
  Expr.resolveInterfaceIdsFuel defaultResolveInterfaceIdsFuel env expr

def Arg.resolveInterfaceIds (env : InterfaceIdEnv) (arg : Arg) : Arg :=
  Arg.resolveInterfaceIdsFuel defaultResolveInterfaceIdsFuel env arg

def ModifierInvocation.resolveInterfaceIds (env : InterfaceIdEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with args := invocation.args.map (Arg.resolveInterfaceIds env) }

def StateVarDecl.resolveInterfaceIds (env : InterfaceIdEnv)
    (decl : StateVarDecl) : StateVarDecl :=
  { decl with init := decl.init.map (Expr.resolveInterfaceIds env) }

mutual

def Stmt.resolveInterfaceIdsFuel : Nat -> InterfaceIdEnv -> Stmt -> Stmt
  | 0, _, stmt => stmt
  | fuel + 1, env, stmt =>
      let resolveStmt := Stmt.resolveInterfaceIdsFuel fuel env
      let resolveExpr := Expr.resolveInterfaceIdsFuel fuel env
      let resolveClause := CatchClause.resolveInterfaceIdsFuel fuel env
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body => Stmt.block (body.map resolveStmt)
      | Stmt.varDecl bindings init =>
          Stmt.varDecl bindings (init.map resolveExpr)
      | Stmt.expr expr => Stmt.expr (resolveExpr expr)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (resolveExpr cond) (resolveStmt thenBranch)
            (elseBranch.map resolveStmt)
      | Stmt.whileLoop cond body =>
          Stmt.whileLoop (resolveExpr cond) (resolveStmt body)
      | Stmt.doWhile body cond =>
          Stmt.doWhile (resolveStmt body) (resolveExpr cond)
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map resolveStmt) (cond.map resolveExpr)
            (post.map resolveExpr) (resolveStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch (resolveExpr expr) (clauses.map resolveClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          Stmt.tryCatchReturns (resolveExpr expr) returns
            (resolveStmt success) (clauses.map resolveClause)
      | Stmt.emitEvent expr => Stmt.emitEvent (resolveExpr expr)
      | Stmt.revertCall expr => Stmt.revertCall (resolveExpr expr)
      | Stmt.returnValues expr? => Stmt.returnValues (expr?.map resolveExpr)
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (resolveStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.resolveInterfaceIdsFuel :
    Nat -> InterfaceIdEnv -> CatchClause -> CatchClause
  | 0, _, clause => clause
  | fuel + 1, env, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name params
            (Stmt.resolveInterfaceIdsFuel fuel env body)

end

def Stmt.resolveInterfaceIds (env : InterfaceIdEnv) (stmt : Stmt) : Stmt :=
  Stmt.resolveInterfaceIdsFuel defaultResolveInterfaceIdsFuel env stmt

def FunctionDecl.resolveInterfaceIds (env : InterfaceIdEnv)
    (decl : FunctionDecl) : FunctionDecl :=
  { decl with
    modifiers := decl.modifiers.map (ModifierInvocation.resolveInterfaceIds env)
    body := decl.body.map (Stmt.resolveInterfaceIds env) }

def ModifierDecl.resolveInterfaceIds (env : InterfaceIdEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  { decl with body := decl.body.map (Stmt.resolveInterfaceIds env) }

mutual

def Expr.resolveSelectorsFuel : Nat -> SelectorEnv -> Expr -> Expr
  | 0, _, expr => expr
  | fuel + 1, env, expr =>
      let resolve := Expr.resolveSelectorsFuel fuel env
      let resolveArg := Arg.resolveSelectorsFuel fuel env
      let resolveOption := CallOption.resolveSelectorsFuel fuel env
      let resolveTupleItem := TupleItem.resolveSelectorsFuel fuel env
      match expr with
      | Expr.member (Expr.ident name) "selector" =>
          match SelectorEnv.lookup? env name with
          | some selector => selectorLiteralExpr selector
          | none => expr
      | Expr.member (Expr.member base name) "selector" =>
          match SelectorEnv.lookup? env name with
          | some selector => selectorLiteralExpr selector
          | none => Expr.member (Expr.member (resolve base) name) "selector"
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (resolve base) member
      | Expr.index base index => Expr.index (resolve base) (resolve index)
      | Expr.slice base start stop =>
          Expr.slice (resolve base) (start.map resolve) (stop.map resolve)
      | Expr.call fn args =>
          Expr.call (resolve fn) (args.map resolveArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (resolve fn)
            (options.map resolveOption) (args.map resolveArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map resolveArg)
      | Expr.tuple items => Expr.tuple (items.map resolveTupleItem)
      | Expr.array exprs => Expr.array (exprs.map resolve)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (resolve inner)
      | Expr.unary op inner => Expr.unary op (resolve inner)
      | Expr.binary op lhs rhs =>
          Expr.binary op (resolve lhs) (resolve rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (resolve cond) (resolve thenExpr) (resolve elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (resolve lhs) op (resolve rhs)
      | Expr.payableConversion inner => Expr.payableConversion (resolve inner)

def Arg.resolveSelectorsFuel :
    Nat -> SelectorEnv -> Arg -> Arg
  | 0, _, arg => arg
  | fuel + 1, env, arg =>
      let resolve := Expr.resolveSelectorsFuel fuel env
      match arg with
      | Arg.positional expr => Arg.positional (resolve expr)
      | Arg.named name expr => Arg.named name (resolve expr)

def CallOption.resolveSelectorsFuel :
    Nat -> SelectorEnv -> CallOption -> CallOption
  | 0, _, option => option
  | fuel + 1, env, option =>
      let resolve := Expr.resolveSelectorsFuel fuel env
      match option with
      | CallOption.named name expr => CallOption.named name (resolve expr)

def TupleItem.resolveSelectorsFuel :
    Nat -> SelectorEnv -> TupleItem -> TupleItem
  | 0, _, item => item
  | fuel + 1, env, item =>
      let resolve := Expr.resolveSelectorsFuel fuel env
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (resolve expr)

end

def defaultResolveSelectorsFuel : Nat := 1024

def Expr.resolveSelectors (env : SelectorEnv) (expr : Expr) : Expr :=
  Expr.resolveSelectorsFuel defaultResolveSelectorsFuel env expr

def Arg.resolveSelectors (env : SelectorEnv) (arg : Arg) : Arg :=
  Arg.resolveSelectorsFuel defaultResolveSelectorsFuel env arg

def ModifierInvocation.resolveSelectors (env : SelectorEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with args := invocation.args.map (Arg.resolveSelectors env) }

def StateVarDecl.resolveSelectors (env : SelectorEnv)
    (decl : StateVarDecl) : StateVarDecl :=
  { decl with init := decl.init.map (Expr.resolveSelectors env) }

mutual

def Stmt.resolveSelectorsFuel : Nat -> SelectorEnv -> Stmt -> Stmt
  | 0, _, stmt => stmt
  | fuel + 1, env, stmt =>
      let resolveStmt := Stmt.resolveSelectorsFuel fuel env
      let resolveExpr := Expr.resolveSelectorsFuel fuel env
      let resolveClause := CatchClause.resolveSelectorsFuel fuel env
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body => Stmt.block (body.map resolveStmt)
      | Stmt.varDecl bindings init =>
          Stmt.varDecl bindings (init.map resolveExpr)
      | Stmt.expr expr => Stmt.expr (resolveExpr expr)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (resolveExpr cond) (resolveStmt thenBranch)
            (elseBranch.map resolveStmt)
      | Stmt.whileLoop cond body =>
          Stmt.whileLoop (resolveExpr cond) (resolveStmt body)
      | Stmt.doWhile body cond =>
          Stmt.doWhile (resolveStmt body) (resolveExpr cond)
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map resolveStmt) (cond.map resolveExpr)
            (post.map resolveExpr) (resolveStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch (resolveExpr expr) (clauses.map resolveClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          Stmt.tryCatchReturns (resolveExpr expr) returns
            (resolveStmt success) (clauses.map resolveClause)
      | Stmt.emitEvent expr => Stmt.emitEvent (resolveExpr expr)
      | Stmt.revertCall expr => Stmt.revertCall (resolveExpr expr)
      | Stmt.returnValues expr? => Stmt.returnValues (expr?.map resolveExpr)
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (resolveStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.resolveSelectorsFuel :
    Nat -> SelectorEnv -> CatchClause -> CatchClause
  | 0, _, clause => clause
  | fuel + 1, env, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name params
            (Stmt.resolveSelectorsFuel fuel env body)

end

def Stmt.resolveSelectors (env : SelectorEnv) (stmt : Stmt) : Stmt :=
  Stmt.resolveSelectorsFuel defaultResolveSelectorsFuel env stmt

def FunctionDecl.resolveSelectors (env : SelectorEnv)
    (decl : FunctionDecl) : FunctionDecl :=
  { decl with
    modifiers := decl.modifiers.map (ModifierInvocation.resolveSelectors env)
    body := decl.body.map (Stmt.resolveSelectors env) }

def ModifierDecl.resolveSelectors (env : SelectorEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  { decl with body := decl.body.map (Stmt.resolveSelectors env) }

def ContractItem.resolveSelectors (env : SelectorEnv) :
    ContractItem -> ContractItem
  | ContractItem.stateVar decl =>
      ContractItem.stateVar (StateVarDecl.resolveSelectors env decl)
  | ContractItem.function decl =>
      ContractItem.function (FunctionDecl.resolveSelectors env decl)
  | ContractItem.modifierDecl decl =>
      ContractItem.modifierDecl (ModifierDecl.resolveSelectors env decl)
  | other => other

def ContractDecl.resolveSelectors (env : SelectorEnv)
    (decl : ContractDecl) : ContractDecl :=
  { decl with items := decl.items.map (ContractItem.resolveSelectors env) }

mutual

def Expr.resolveFunctionAddressesFuel : Nat -> SelectorEnv -> Expr -> Expr
  | 0, _, expr => expr
  | fuel + 1, env, expr =>
      let resolve := Expr.resolveFunctionAddressesFuel fuel env
      let resolveArg := Arg.resolveFunctionAddressesFuel fuel env
      let resolveOption := CallOption.resolveFunctionAddressesFuel fuel env
      let resolveTupleItem := TupleItem.resolveFunctionAddressesFuel fuel env
      match expr with
      | Expr.member (Expr.member base name) "address" =>
          match SelectorEnv.lookup? env name with
          | some _ => resolve base
          | none => Expr.member (Expr.member (resolve base) name) "address"
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (resolve base) member
      | Expr.index base index => Expr.index (resolve base) (resolve index)
      | Expr.slice base start stop =>
          Expr.slice (resolve base) (start.map resolve) (stop.map resolve)
      | Expr.call fn args =>
          Expr.call (resolve fn) (args.map resolveArg)
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (resolve fn)
            (options.map resolveOption) (args.map resolveArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map resolveArg)
      | Expr.tuple items => Expr.tuple (items.map resolveTupleItem)
      | Expr.array exprs => Expr.array (exprs.map resolve)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (resolve inner)
      | Expr.unary op inner => Expr.unary op (resolve inner)
      | Expr.binary op lhs rhs =>
          Expr.binary op (resolve lhs) (resolve rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (resolve cond) (resolve thenExpr) (resolve elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (resolve lhs) op (resolve rhs)
      | Expr.payableConversion inner => Expr.payableConversion (resolve inner)

def Arg.resolveFunctionAddressesFuel :
    Nat -> SelectorEnv -> Arg -> Arg
  | 0, _, arg => arg
  | fuel + 1, env, arg =>
      let resolve := Expr.resolveFunctionAddressesFuel fuel env
      match arg with
      | Arg.positional expr => Arg.positional (resolve expr)
      | Arg.named name expr => Arg.named name (resolve expr)

def CallOption.resolveFunctionAddressesFuel :
    Nat -> SelectorEnv -> CallOption -> CallOption
  | 0, _, option => option
  | fuel + 1, env, option =>
      let resolve := Expr.resolveFunctionAddressesFuel fuel env
      match option with
      | CallOption.named name expr => CallOption.named name (resolve expr)

def TupleItem.resolveFunctionAddressesFuel :
    Nat -> SelectorEnv -> TupleItem -> TupleItem
  | 0, _, item => item
  | fuel + 1, env, item =>
      let resolve := Expr.resolveFunctionAddressesFuel fuel env
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (resolve expr)

end

def defaultResolveFunctionAddressesFuel : Nat := 1024

def Expr.resolveFunctionAddresses (env : SelectorEnv) (expr : Expr) : Expr :=
  Expr.resolveFunctionAddressesFuel
    defaultResolveFunctionAddressesFuel env expr

def Arg.resolveFunctionAddresses (env : SelectorEnv) (arg : Arg) : Arg :=
  Arg.resolveFunctionAddressesFuel defaultResolveFunctionAddressesFuel env arg

def ModifierInvocation.resolveFunctionAddresses (env : SelectorEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with
    args := invocation.args.map (Arg.resolveFunctionAddresses env) }

def StateVarDecl.resolveFunctionAddresses (env : SelectorEnv)
    (decl : StateVarDecl) : StateVarDecl :=
  { decl with init := decl.init.map (Expr.resolveFunctionAddresses env) }

mutual

def Stmt.resolveFunctionAddressesFuel :
    Nat -> SelectorEnv -> Stmt -> Stmt
  | 0, _, stmt => stmt
  | fuel + 1, env, stmt =>
      let resolveStmt := Stmt.resolveFunctionAddressesFuel fuel env
      let resolveExpr := Expr.resolveFunctionAddressesFuel fuel env
      let resolveClause := CatchClause.resolveFunctionAddressesFuel fuel env
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body => Stmt.block (body.map resolveStmt)
      | Stmt.varDecl bindings init =>
          Stmt.varDecl bindings (init.map resolveExpr)
      | Stmt.expr expr => Stmt.expr (resolveExpr expr)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse (resolveExpr cond) (resolveStmt thenBranch)
            (elseBranch.map resolveStmt)
      | Stmt.whileLoop cond body =>
          Stmt.whileLoop (resolveExpr cond) (resolveStmt body)
      | Stmt.doWhile body cond =>
          Stmt.doWhile (resolveStmt body) (resolveExpr cond)
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map resolveStmt) (cond.map resolveExpr)
            (post.map resolveExpr) (resolveStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch (resolveExpr expr) (clauses.map resolveClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          Stmt.tryCatchReturns (resolveExpr expr) returns
            (resolveStmt success) (clauses.map resolveClause)
      | Stmt.emitEvent expr => (Stmt.emitEvent (resolveExpr expr))
      | Stmt.revertCall expr => (Stmt.revertCall (resolveExpr expr))
      | Stmt.returnValues expr? => Stmt.returnValues (expr?.map resolveExpr)
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (resolveStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.resolveFunctionAddressesFuel :
    Nat -> SelectorEnv -> CatchClause -> CatchClause
  | 0, _, clause => clause
  | fuel + 1, env, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name params
            (Stmt.resolveFunctionAddressesFuel fuel env body)

end

def Stmt.resolveFunctionAddresses (env : SelectorEnv) (stmt : Stmt) : Stmt :=
  Stmt.resolveFunctionAddressesFuel
    defaultResolveFunctionAddressesFuel env stmt

def FunctionDecl.resolveFunctionAddresses (env : SelectorEnv)
    (decl : FunctionDecl) : FunctionDecl :=
  { decl with
    modifiers :=
      decl.modifiers.map (ModifierInvocation.resolveFunctionAddresses env)
    body := decl.body.map (Stmt.resolveFunctionAddresses env) }

def ModifierDecl.resolveFunctionAddresses (env : SelectorEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  { decl with body := decl.body.map (Stmt.resolveFunctionAddresses env) }

def ContractItem.resolveFunctionAddresses (env : SelectorEnv) :
    ContractItem -> ContractItem
  | ContractItem.stateVar decl =>
      ContractItem.stateVar (StateVarDecl.resolveFunctionAddresses env decl)
  | ContractItem.function decl =>
      ContractItem.function (FunctionDecl.resolveFunctionAddresses env decl)
  | ContractItem.modifierDecl decl =>
      ContractItem.modifierDecl (ModifierDecl.resolveFunctionAddresses env decl)
  | other => other

def ContractDecl.resolveFunctionAddresses (env : SelectorEnv)
    (decl : ContractDecl) : ContractDecl :=
  { decl with
    items := decl.items.map (ContractItem.resolveFunctionAddresses env) }

def Args.toPositionalExprs? : List Arg -> Option (List Expr)
  | [] => some []
  | Arg.positional expr :: rest => do
      let tail ← Args.toPositionalExprs? rest
      some (expr :: tail)
  | Arg.named _ _ :: _ => none

def Args.namedNames? : List Arg -> Option (List Name)
  | [] => some []
  | Arg.named name _ :: rest => do
      let tail ← Args.namedNames? rest
      some (name :: tail)
  | Arg.positional _ :: _ => none

def Args.toNamedExprsForParams? (params : List Parameter)
    (args : List Arg) : Option (List Expr) := do
  let names ← Args.namedNames? args
  if params.length == args.length && namesUnique names then
    mapOption
      (fun param => do
        let name ← param.name
        Args.findNamed? name args)
      params
  else
    none

def Args.toExprsForParams? (params : List Parameter)
    (args : List Arg) : Option (List Expr) :=
  match Args.toPositionalExprs? args with
  | some exprs =>
      if params.length == exprs.length then
        some exprs
      else
        none
  | none => Args.toNamedExprsForParams? params args

def modifierParamBindingsWithArgs? (decl : SourceModifierDecl)
    (args : List Arg) : Option (List Stmt) := do
  let orderedArgs ← Args.toExprsForParams? decl.params args
  some
    (decl.params.zip orderedArgs |>.map
      (fun pair =>
        let param := pair.fst
        let arg := pair.snd
        Stmt.varDecl
          [{ name := param.name
             ty := some param.ty
             location := param.location }]
          (some arg)))

def modifierApply? (decl : SourceModifierDecl)
    (invocation : SourceModifierInvocation) (inner : Stmt) : Option Stmt := do
  let body ← decl.body
  let prefixStmts ← modifierParamBindingsWithArgs? decl invocation.args
  some
    (Stmt.block
      (prefixStmts ++ [Stmt.replaceTopLevelModifierPlaceholder inner body]))

def modifierFindByName? (modifiers : List SourceModifierDecl)
    (name : Name) : Option SourceModifierDecl :=
  modifiers.find? (fun modifier => modifier.name == name)

def functionExpandModifiers? (available : List SourceModifierDecl)
    (invocations : List SourceModifierInvocation) (body : Stmt) : Option Stmt :=
  match invocations with
  | [] => some body
  | invocation :: rest => do
      let inner ← functionExpandModifiers? available rest body
      let modifierName ← pathLast? invocation.target
      let modifierDecl ← modifierFindByName? available modifierName
      modifierApply? modifierDecl invocation inner

def modifierApplyToCore? (storageNames returnNames : List Name)
    (decl : SourceModifierDecl)
    (invocation : SourceModifierInvocation) (inner : CoreStmt) :
    Option CoreStmt := do
  let body ← decl.body
  let prefixStmts ← modifierParamBindingsWithArgs? decl invocation.args
  let prefixCore ← Stmt.listToCore? storageNames prefixStmts
  let bodyCore ←
    Stmt.toCoreReplacingModifierPlaceholder?
      storageNames returnNames inner body
  some (SolidCore.Solidity.Source.Stmt.block (prefixCore ++ [bodyCore]))

def functionExpandModifiersToCore? (storageNames returnNames : List Name)
    (available : List SourceModifierDecl)
    (invocations : List SourceModifierInvocation) (body : Stmt) :
    Option CoreStmt :=
  match invocations with
  | [] => Stmt.toCore? storageNames body
  | invocation :: rest => do
      let inner ←
        functionExpandModifiersToCore?
          storageNames returnNames available rest body
      let modifierName ← pathLast? invocation.target
      let modifierDecl ← modifierFindByName? available modifierName
      modifierApplyToCore? storageNames returnNames
        modifierDecl invocation inner

def FunctionDecl.isConstructor (decl : FunctionDecl) : Bool :=
  match decl.kind with
  | FunctionKind.constructor => true
  | _ => false

def FunctionDecl.coreName? (decl : FunctionDecl) : Option Name :=
  match decl.kind with
  | FunctionKind.function => decl.name
  | FunctionKind.receive => some "__receive"
  | FunctionKind.fallback => some "__fallback"
  | FunctionKind.constructor => none

def FunctionDecl.isPayable (decl : FunctionDecl) : Bool :=
  match decl.mutability with
  | StateMutability.payable => true
  | _ => false

def FunctionDecl.isExternallyNamedFunction (decl : FunctionDecl) : Bool :=
  match decl.kind with
  | FunctionKind.function => true
  | _ => false

def FunctionDecl.isCoreEntrypoint (decl : FunctionDecl) : Bool :=
  match decl.visibility with
  | some Visibility.internal_
  | some Visibility.private_ => false
  | _ => true

mutual

def Ty.matchesShape : Ty -> Ty -> Bool
  | Ty.bool, Ty.bool => true
  | Ty.address _, Ty.address _ => true
  | Ty.uint lhs, Ty.uint rhs =>
      (lhs == rhs) || (lhs == 0 && rhs == 256) || (lhs == 256 && rhs == 0)
  | Ty.int lhs, Ty.int rhs =>
      (lhs == rhs) || (lhs == 0 && rhs == 256) || (lhs == 256 && rhs == 0)
  | Ty.bytesN lhs, Ty.bytesN rhs => lhs == rhs
  | Ty.fixedBytes lhs, Ty.fixedBytes rhs => lhs == rhs
  | Ty.bytes, Ty.bytes => true
  | Ty.string, Ty.string => true
  | Ty.array lhsTy lhsSize?, Ty.array rhsTy rhsSize? =>
      lhsSize? == rhsSize? && Ty.matchesShape lhsTy rhsTy
  | Ty.tuple lhs, Ty.tuple rhs => Ty.listMatchesShape lhs rhs
  | Ty.user lhs, Ty.user rhs => lhs.segments == rhs.segments
  | _, _ => false

def Ty.listMatchesShape : List Ty -> List Ty -> Bool
  | [], [] => true
  | lhs :: lhsRest, rhs :: rhsRest =>
      Ty.matchesShape lhs rhs && Ty.listMatchesShape lhsRest rhsRest
  | _, _ => false

end

def Parameter.matchesArg? (env : TypeEnv) (param : Parameter)
    (arg : Expr) : Option Bool := do
  let argTy ← Expr.abiTyWithEnv? env arg
  some (Ty.matchesShape argTy param.ty)

def Parameters.matchArgsWithEnv? (env : TypeEnv) :
    List Parameter -> List Expr -> Option Bool
  | [], [] => some true
  | param :: params, arg :: args => do
      let head ← Parameter.matchesArg? env param arg
      let tail ← Parameters.matchArgsWithEnv? env params args
      some (head && tail)
  | _, _ => some false

def FunctionDecl.findInternalCallee? (functions : List FunctionDecl)
    (env : TypeEnv) (name : Name) (args : List Expr) :
    Option FunctionDecl :=
  let candidates :=
    functions.filter (fun fn =>
      match fn.name with
      | some fnName =>
          fnName == name && fn.params.length == args.length &&
            FunctionDecl.isExternallyNamedFunction fn
      | none => false)
  match candidates.find? (fun fn =>
      match Parameters.matchArgsWithEnv? env fn.params args with
      | some true => true
      | _ => false) with
  | some fn => some fn
  | none => candidates.head?

def FunctionDecl.orderedArgs? (decl : FunctionDecl)
    (args : List Arg) : Option (List Expr) :=
  Args.toExprsForParams? decl.params args

def FunctionDecl.findInternalCalleeWithArgs?
    (functions : List FunctionDecl) (env : TypeEnv)
    (name : Name) (args : List Arg) :
    Option (FunctionDecl × List Expr) :=
  let candidates :=
    functions.filter (fun fn =>
      match fn.name with
      | some fnName =>
          fnName == name && fn.params.length == args.length &&
            FunctionDecl.isExternallyNamedFunction fn
      | none => false)
  match candidates.find? (fun fn =>
      match FunctionDecl.orderedArgs? fn args with
      | some orderedArgs =>
          match Parameters.matchArgsWithEnv? env fn.params orderedArgs with
          | some true => true
          | _ => false
      | none => false) with
  | some fn => do
      let orderedArgs ← FunctionDecl.orderedArgs? fn args
      some (fn, orderedArgs)
  | none => do
      let fn ← candidates.find?
        (fun candidate =>
          match FunctionDecl.orderedArgs? candidate args with
          | some _ => true
          | none => false)
      let orderedArgs ← FunctionDecl.orderedArgs? fn args
      some (fn, orderedArgs)

def Expr.storageRefArrayMemberStmtCore?
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) :
    Expr -> Option CoreStmt
  | Expr.call (Expr.member (Expr.ident name) "push") [] => do
      if stateNameIsStorage name storageNames then
        none
      else
        some ()
      if StorageRefEnv.isStorageRef storageRefEnv name then
        some ()
      else
        none
      let ty ← TypeEnv.lookup? env name
      if Ty.hasStorageArrayMembers ty then
        some (SolidCore.Solidity.Source.Stmt.storageArrayPushRef name none)
      else
        none
  | Expr.call (Expr.member (Expr.ident name) "push")
      [Arg.positional value] => do
      if stateNameIsStorage name storageNames then
        none
      else
        some ()
      if StorageRefEnv.isStorageRef storageRefEnv name then
        some ()
      else
        none
      let ty ← TypeEnv.lookup? env name
      if Ty.hasStorageArrayMembers ty then
        let valueCore ← Expr.toCore? storageNames value
        some
          (SolidCore.Solidity.Source.Stmt.storageArrayPushRef
            name (some valueCore))
      else
        none
  | Expr.call (Expr.member (Expr.ident name) "pop") [] => do
      if stateNameIsStorage name storageNames then
        none
      else
        some ()
      if StorageRefEnv.isStorageRef storageRefEnv name then
        some ()
      else
        none
      let ty ← TypeEnv.lookup? env name
      if Ty.hasStorageArrayMembers ty then
        some (SolidCore.Solidity.Source.Stmt.storageArrayPopRef name)
      else
        none
  | _ => none

def Expr.storageRefArrayPushAssignStmtCore?
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) (name : Name) (rhs : Expr) :
    Option CoreStmt := do
  if stateNameIsStorage name storageNames then
    none
  else
    some ()
  if StorageRefEnv.isStorageRef storageRefEnv name then
    some ()
  else
    none
  let ty ← TypeEnv.lookup? env name
  if Ty.hasStorageArrayMembers ty then
    some ()
  else
    none
  let rhsCore ← Expr.toCore? storageNames rhs
  let lastIndex :=
    SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.sub
      (SolidCore.Solidity.Source.Expr.var name)
      (SolidCore.Solidity.Source.Expr.word 1)
  some
    (SolidCore.Solidity.Source.Stmt.block
      [ SolidCore.Solidity.Source.Stmt.storageArrayPushRef name none
      , SolidCore.Solidity.Source.Stmt.assign
          (SolidCore.Solidity.Source.LValue.index
            (SolidCore.Solidity.Source.LValue.var name)
            lastIndex)
          rhsCore ])

def storageAliasDeclFromRefCore? (storageRefEnv : StorageRefEnv)
    (binding : VarBinding) (source : Name) : Option CoreStmt :=
  match binding.name, binding.location with
  | some name, some DataLocation.storage =>
      if StorageRefEnv.isStorageRef storageRefEnv source then
        some (SolidCore.Solidity.Source.Stmt.storageAliasFrom name source)
      else
        none
  | _, _ => none

def storageAliasAssignmentCore? (storageRefEnv : StorageRefEnv)
    (storageNames : List Name) (name target : Name) : Option CoreStmt :=
  if StorageRefEnv.isStorageRef storageRefEnv name then
    if stateNameIsStorage target storageNames then
      some (SolidCore.Solidity.Source.Stmt.storageAliasAssign name target)
    else if StorageRefEnv.isStorageRef storageRefEnv target then
      some (SolidCore.Solidity.Source.Stmt.storageAliasAssignFrom name target)
    else
      none
  else
    none

mutual

def Stmt.toCoreWithStorageRefsOnly? (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (storageNames : List Name) (stmt : Stmt) :
    Option CoreStmt :=
  match stmt with
  | Stmt.block body => do
      let coreBody ←
        Stmt.listToCoreWithStorageRefsOnly?
          storageRefEnv env storageNames body
      some (SolidCore.Solidity.Source.Stmt.block coreBody)
  | Stmt.expr
      (Expr.assign
        (Expr.call (Expr.member (Expr.ident name) "push") [])
        AssignOp.assign rhs) =>
      match Expr.storageRefArrayPushAssignStmtCore?
          storageRefEnv env storageNames name rhs with
      | some coreStmt => some coreStmt
      | none => Stmt.toCore? storageNames
          (Stmt.expr
            (Expr.assign
              (Expr.call (Expr.member (Expr.ident name) "push") [])
              AssignOp.assign rhs))
  | Stmt.expr expr@(Expr.call (Expr.member _ _) _) =>
      match Stmt.toCore? storageNames (Stmt.expr expr) with
      | some coreStmt => some coreStmt
      | none =>
          Expr.storageRefArrayMemberStmtCore?
            storageRefEnv env storageNames expr
  | Stmt.ifElse cond thenBranch elseBranch => do
      let condCore ← Expr.toCore? storageNames cond
      let thenCore ←
        Stmt.toCoreWithStorageRefsOnly?
          storageRefEnv env storageNames thenBranch
      let elseCore ←
        match elseBranch with
        | some stmt =>
            Stmt.toCoreWithStorageRefsOnly?
              storageRefEnv env storageNames stmt
        | none => some SolidCore.Solidity.Source.Stmt.skip
      some (SolidCore.Solidity.Source.Stmt.ifElse
        condCore thenCore elseCore)
  | Stmt.whileLoop cond body => do
      let condCore ← Expr.toCore? storageNames cond
      let bodyCore ←
        Stmt.toCoreWithStorageRefsOnly?
          storageRefEnv env storageNames body
      some (SolidCore.Solidity.Source.Stmt.whileLoop condCore bodyCore)
  | Stmt.doWhile body cond => do
      let bodyCore ←
        Stmt.toCoreWithStorageRefsOnly?
          storageRefEnv env storageNames body
      let condCore ← Expr.toCore? storageNames cond
      some (SolidCore.Solidity.Source.Stmt.doWhile bodyCore condCore)
  | Stmt.forLoop init cond post body => do
      let initCore ←
        match init with
        | some stmt =>
            Stmt.toCoreWithStorageRefsOnly?
              storageRefEnv env storageNames stmt
        | none => some SolidCore.Solidity.Source.Stmt.skip
      let condCore ←
        match cond with
        | some expr => Expr.toCore? storageNames expr
        | none => some (SolidCore.Solidity.Source.Expr.word 1)
      let postCore ←
        match post with
        | some expr => Stmt.toCore? storageNames (Stmt.expr expr)
        | none => some SolidCore.Solidity.Source.Stmt.skip
      let bodyCore ←
        Stmt.toCoreWithStorageRefsOnly?
          storageRefEnv env storageNames body
      some (SolidCore.Solidity.Source.Stmt.forLoop
        initCore condCore postCore bodyCore)
  | Stmt.unchecked body => do
      let bodyCore ←
        Stmt.toCoreWithStorageRefsOnly?
          storageRefEnv env storageNames body
      some (SolidCore.Solidity.Source.Stmt.unchecked bodyCore)
  | other => Stmt.toCore? storageNames other
termination_by (sizeOf stmt, 2)

def Stmt.listToCoreWithStorageRefsOnly? (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (storageNames : List Name) (stmts : List Stmt) :
    Option (List CoreStmt) :=
  match stmts with
  | [] => some []
  | Stmt.expr (Expr.assign (Expr.ident name) AssignOp.assign
      (Expr.ident target)) :: rest =>
      match storageAliasAssignmentCore? storageRefEnv storageNames name target with
      | some head => do
          let tail ←
            Stmt.listToCoreWithStorageRefsOnly?
              storageRefEnv env storageNames rest
          some (head :: tail)
      | none => do
          let head ←
            Stmt.toCoreWithStorageRefsOnly?
              storageRefEnv env storageNames
              (Stmt.expr
                (Expr.assign (Expr.ident name) AssignOp.assign
                  (Expr.ident target)))
          let tail ←
            Stmt.listToCoreWithStorageRefsOnly?
              storageRefEnv env storageNames rest
          some (head :: tail)
  | Stmt.varDecl [binding] (some (Expr.ident source)) :: rest =>
      match storageAliasDeclFromRefCore? storageRefEnv binding source with
      | some head => do
          let tail ←
            Stmt.listToCoreWithStorageRefsOnly?
              (VarBinding.extendStorageRefEnv storageRefEnv binding)
              (VarBinding.extendTypeEnv env binding)
              storageNames rest
          some (head :: tail)
      | none => do
          let head ←
            Stmt.toCoreWithStorageRefsOnly?
              storageRefEnv env storageNames
              (Stmt.varDecl [binding] (some (Expr.ident source)))
          let tail ←
            Stmt.listToCoreWithStorageRefsOnly?
              (VarBinding.extendStorageRefEnv storageRefEnv binding)
              (VarBinding.extendTypeEnv env binding)
              storageNames rest
          some (head :: tail)
  | stmt :: rest => do
      let head ←
        Stmt.toCoreWithStorageRefsOnly? storageRefEnv env storageNames stmt
      let nextEnv :=
        match stmt with
        | Stmt.varDecl bindings _ => VarBindings.extendTypeEnv env bindings
        | _ => env
      let nextStorageRefEnv :=
        match stmt with
        | Stmt.varDecl bindings _ =>
            VarBindings.extendStorageRefEnv storageRefEnv bindings
        | _ => storageRefEnv
      let tail ←
        Stmt.listToCoreWithStorageRefsOnly?
          nextStorageRefEnv nextEnv storageNames rest
      some (head :: tail)
termination_by (sizeOf stmts, 1)

end

def functionExpandModifiersToCoreWithStorageRefsOnly?
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames returnNames : List Name)
    (available : List SourceModifierDecl)
    (invocations : List SourceModifierInvocation) (body : Stmt) :
    Option CoreStmt :=
  match invocations with
  | [] =>
      Stmt.toCoreWithStorageRefsOnly?
        storageRefEnv env storageNames body
  | invocation :: rest => do
      let inner ←
        functionExpandModifiersToCoreWithStorageRefsOnly?
          storageRefEnv env storageNames returnNames available rest body
      let modifierName ← pathLast? invocation.target
      let modifierDecl ← modifierFindByName? available modifierName
      modifierApplyToCore? storageNames returnNames
        modifierDecl invocation inner

def Expr.localStorageArrayMemberStmtCore?
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) :
    Expr -> Option CoreStmt :=
  Expr.storageRefArrayMemberStmtCore? storageRefEnv env storageNames

def defaultInternalCallInlineFuel : Nat := 64

mutual

def functionExpandModifiersToCoreWithInternalCalls?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames returnNames : List Name)
    (available : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (invocations : List SourceModifierInvocation) (body : Stmt) :
    Option CoreStmt :=
  match invocations with
  | [] =>
      Stmt.toCoreWithInternalCalls?
        (internalFuel := internalFuel)
        (storageRefEnv := storageRefEnv)
        (env := env)
        (storageNames := storageNames)
        (modifiers := available)
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := body)
  | invocation :: rest => do
      let inner ←
        functionExpandModifiersToCoreWithInternalCalls?
          internalFuel storageRefEnv env storageNames returnNames available
          functions freeFunctions returnTys rest body
      let modifierName ← pathLast? invocation.target
      let modifierDecl ← modifierFindByName? available modifierName
      modifierApplyToCore? storageNames returnNames
        modifierDecl invocation inner
termination_by (internalFuel, sizeOf invocations + sizeOf body, 6)

def FunctionDecl.internalCallParts?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg) :
    Option (List CoreBindingDecl × List CoreStmt × CoreStmt) := do
  match FunctionDecl.findInternalCalleeWithArgs?
      functions env name args with
  | some (callee, sourceArgs) => do
      let paramDecls ←
        Parameters.toStorageAwareCoreArgDecls?
          storageRefEnv storageNames "_arg" callee.params sourceArgs
      let returnDecls := Parameters.toDefaultVarDecls "_ret" callee.returns
      let returnBindings ← Parameters.toCoreBindings? "_ret" callee.returns
      let body ← callee.body
      let calleeEnv := FunctionDecl.typeEnv [] callee
      let calleeStorageRefEnv :=
        Parameters.extendStorageRefEnv "_arg" [] callee.params
      let body := Stmt.annotateAbi calleeEnv body
      let bodyCore ←
        match internalFuel with
        | 0 =>
            functionExpandModifiersToCoreWithStorageRefsOnly?
              calleeStorageRefEnv calleeEnv storageNames
              (returnBindings.map SolidCore.Solidity.Source.BindingDecl.name)
              modifiers callee.modifiers body
        | fuel + 1 =>
            functionExpandModifiersToCoreWithInternalCalls?
              fuel calleeStorageRefEnv calleeEnv storageNames
              (returnBindings.map SolidCore.Solidity.Source.BindingDecl.name)
              modifiers functions freeFunctions
              (callee.returns.map Parameter.ty) callee.modifiers body
      let prefixCore ←
        Stmt.listToCore? storageNames returnDecls
      let prefixCore := paramDecls ++ prefixCore
      some (returnBindings, prefixCore, bodyCore)
  | none => do
      let (callee, sourceArgs) ←
        FunctionDecl.findInternalCalleeWithArgs?
          freeFunctions env name args
      let paramDecls ←
        Parameters.toStorageAwareCoreArgDecls?
          storageRefEnv storageNames "_arg" callee.params sourceArgs
      let returnDecls := Parameters.toDefaultVarDecls "_ret" callee.returns
      let returnBindings ← Parameters.toCoreBindings? "_ret" callee.returns
      let body ← callee.body
      let calleeEnv := FunctionDecl.typeEnv [] callee
      let calleeStorageRefEnv :=
        Parameters.extendStorageRefEnv "_arg" [] callee.params
      let body := Stmt.annotateAbi calleeEnv body
      let bodyCore ←
        match internalFuel with
        | 0 =>
            functionExpandModifiersToCoreWithStorageRefsOnly?
              calleeStorageRefEnv calleeEnv []
              (returnBindings.map SolidCore.Solidity.Source.BindingDecl.name)
              [] callee.modifiers body
        | fuel + 1 =>
            functionExpandModifiersToCoreWithInternalCalls?
              fuel calleeStorageRefEnv calleeEnv []
              (returnBindings.map SolidCore.Solidity.Source.BindingDecl.name)
              [] [] freeFunctions
              (callee.returns.map Parameter.ty) callee.modifiers body
      let prefixCore ←
        Stmt.listToCore? storageNames returnDecls
      let prefixCore := paramDecls ++ prefixCore
      some (returnBindings, prefixCore, bodyCore)
termination_by (internalFuel, 0, 0)

def FunctionDecl.internalStatementCallCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg) :
    Option CoreStmt := do
  let (_, prefixCore, bodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
      name args
  some
    (SolidCore.Solidity.Source.Stmt.block
      (prefixCore ++
        [SolidCore.Solidity.Source.Stmt.captureReturn [] bodyCore]))
termination_by (internalFuel, 0, 1)

def FunctionDecl.internalSingleReturnCallCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg)
    (useResult : CoreExpr -> CoreStmt) : Option CoreStmt := do
  let (returnBindings, prefixCore, bodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
      name args
  match returnBindings with
  | [ret] =>
      let retName := ret.name
      some
        (SolidCore.Solidity.Source.Stmt.block
          (prefixCore ++
            [ SolidCore.Solidity.Source.Stmt.captureReturn
                [retName] bodyCore
            , useResult (SolidCore.Solidity.Source.Expr.var retName) ]))
  | _ => none
termination_by (internalFuel, 0, 1)

def FunctionDecl.internalAssignReturnCallCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg)
    (targetNames : List Name) : Option CoreStmt := do
  let (returnBindings, prefixCore, bodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
      name args
  if targetNames.length == returnBindings.length then
    let returnNames :=
      returnBindings.map SolidCore.Solidity.Source.BindingDecl.name
    some
      (SolidCore.Solidity.Source.Stmt.block
        (prefixCore ++
          [ SolidCore.Solidity.Source.Stmt.captureReturn
              returnNames bodyCore ] ++
          CoreBindingDecls.assignToVars targetNames returnBindings))
  else
    none
termination_by (internalFuel, 0, 1)

def Stmt.toCoreWithInternalCalls? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (storageNames : List Name)
    (modifiers : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl) (returnTys : List Ty) (stmt : Stmt) :
    Option CoreStmt :=
  match stmt with
  | Stmt.block body => do
      let coreBody ←
        Stmt.listToCoreWithInternalCallsWithRefs?
          internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
          returnTys body
      some (SolidCore.Solidity.Source.Stmt.block coreBody)
  | Stmt.expr expr@(Expr.call (Expr.member _ _) _) =>
      match Stmt.toCore? storageNames (Stmt.expr expr) with
      | some coreStmt => some coreStmt
      | none =>
          match Expr.localStorageArrayMemberStmtCore?
              storageRefEnv env storageNames expr with
          | some coreStmt => some coreStmt
          | none => Expr.externalCallDiscardCore? storageNames expr
  | Stmt.expr expr@(Expr.callWithOptions (Expr.member _ _) _ _) =>
      match Stmt.toCore? storageNames (Stmt.expr expr) with
      | some coreStmt => some coreStmt
      | none => Expr.externalCallDiscardCore? storageNames expr
  | Stmt.expr
      (Expr.assign
        (Expr.call (Expr.member (Expr.ident name) "push") [])
        AssignOp.assign rhs) =>
      match Expr.storageRefArrayPushAssignStmtCore?
          storageRefEnv env storageNames name rhs with
      | some coreStmt => some coreStmt
      | none => Stmt.toCore? storageNames
          (Stmt.expr
            (Expr.assign
              (Expr.call (Expr.member (Expr.ident name) "push") [])
              AssignOp.assign rhs))
  | Stmt.expr (Expr.call (Expr.ident name) args) =>
      match FunctionDecl.internalStatementCallCore?
          internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
          name args with
      | some coreStmt => some coreStmt
      | none => Stmt.toCore? storageNames
          (Stmt.expr (Expr.call (Expr.ident name) args))
  | Stmt.expr (Expr.assign lhs AssignOp.assign
      expr@(Expr.call (Expr.member _ _) _)) =>
      match Expr.toCoreLValue? storageNames lhs,
          Expr.abiTyWithEnv? env lhs with
      | some lhsCore, some expectedTy =>
          match Expr.externalCallSingleReturnCore?
              storageNames expectedTy expr
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.assign lhsCore retExpr) with
          | some coreStmt => some coreStmt
          | none => Stmt.toCore? storageNames
              (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
      | _, _ => Stmt.toCore? storageNames
          (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
  | Stmt.expr (Expr.assign lhs AssignOp.assign
      expr@(Expr.callWithOptions (Expr.member _ _) _ _)) =>
      match Expr.toCoreLValue? storageNames lhs,
          Expr.abiTyWithEnv? env lhs with
      | some lhsCore, some expectedTy =>
          match Expr.externalCallSingleReturnCore?
              storageNames expectedTy expr
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.assign lhsCore retExpr) with
          | some coreStmt => some coreStmt
          | none => Stmt.toCore? storageNames
              (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
      | _, _ => Stmt.toCore? storageNames
          (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
  | Stmt.expr (Expr.assign lhs AssignOp.assign
      (Expr.call (Expr.ident name) args)) =>
      match Expr.toCoreLValue? storageNames lhs with
      | some lhsCore =>
          match FunctionDecl.internalSingleReturnCallCore?
              internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
              name args
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.assign lhsCore retExpr) with
          | some coreStmt => some coreStmt
          | none => Stmt.toCore? storageNames
              (Stmt.expr
                (Expr.assign lhs AssignOp.assign
                  (Expr.call (Expr.ident name) args)))
      | none => Stmt.toCore? storageNames
          (Stmt.expr
            (Expr.assign lhs AssignOp.assign
              (Expr.call (Expr.ident name) args)))
  | Stmt.varDecl [binding] (some expr@(Expr.call (Expr.member _ _) _)) =>
      match binding.name, binding.ty with
      | some localName, some expectedTy =>
          match Expr.externalCallSingleReturnCore?
              storageNames expectedTy expr
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.assign
                  (SolidCore.Solidity.Source.LValue.var localName)
                  retExpr) with
          | some assignBlock => do
              let declCore ←
                Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
              some
                (SolidCore.Solidity.Source.Stmt.block
                  [declCore, assignBlock])
          | none => Stmt.toCore? storageNames
              (Stmt.varDecl [binding] (some expr))
      | _, _ => Stmt.toCore? storageNames
          (Stmt.varDecl [binding] (some expr))
  | Stmt.varDecl [binding]
      (some expr@(Expr.callWithOptions (Expr.member _ _) _ _)) =>
      match binding.name, binding.ty with
      | some localName, some expectedTy =>
          match Expr.externalCallSingleReturnCore?
              storageNames expectedTy expr
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.assign
                  (SolidCore.Solidity.Source.LValue.var localName)
                  retExpr) with
          | some assignBlock => do
              let declCore ←
                Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
              some
                (SolidCore.Solidity.Source.Stmt.block
                  [declCore, assignBlock])
          | none => Stmt.toCore? storageNames
              (Stmt.varDecl [binding] (some expr))
      | _, _ => Stmt.toCore? storageNames
          (Stmt.varDecl [binding] (some expr))
  | Stmt.varDecl [binding] (some (Expr.call (Expr.ident name) args)) =>
      match binding.name with
      | some localName =>
          match FunctionDecl.internalSingleReturnCallCore?
              internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
              name args
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.assign
                  (SolidCore.Solidity.Source.LValue.var localName)
                  retExpr) with
          | some assignBlock => do
              let declCore ←
                Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
              some
                (SolidCore.Solidity.Source.Stmt.block
                  [declCore, assignBlock])
          | none => Stmt.toCore? storageNames
              (Stmt.varDecl [binding]
                (some (Expr.call (Expr.ident name) args)))
      | none => Stmt.toCore? storageNames
          (Stmt.varDecl [binding]
            (some (Expr.call (Expr.ident name) args)))
  | Stmt.varDecl bindings (some expr@(Expr.call (Expr.member _ _) _)) => do
      let names ← VarBindings.names? bindings
      let returnTys ← VarBindings.sourceTys? bindings
      let decls ← VarBindings.toCoreDecls? bindings
      let callCore ←
        Expr.externalCallAssignVarsCore?
          storageNames returnTys names expr
      some (SolidCore.Solidity.Source.Stmt.block (decls ++ [callCore]))
  | Stmt.varDecl bindings
      (some expr@(Expr.callWithOptions (Expr.member _ _) _ _)) => do
      let names ← VarBindings.names? bindings
      let returnTys ← VarBindings.sourceTys? bindings
      let decls ← VarBindings.toCoreDecls? bindings
      let callCore ←
        Expr.externalCallAssignVarsCore?
          storageNames returnTys names expr
      some (SolidCore.Solidity.Source.Stmt.block (decls ++ [callCore]))
  | Stmt.varDecl bindings (some (Expr.call (Expr.ident name) args)) => do
      let names ← VarBindings.names? bindings
      let decls ← VarBindings.toCoreDecls? bindings
      let callCore ←
        FunctionDecl.internalAssignReturnCallCore?
          internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
          name args names
      some (SolidCore.Solidity.Source.Stmt.block (decls ++ [callCore]))
  | Stmt.returnValues (some expr@(Expr.call (Expr.member _ _) _)) =>
      match Expr.externalCallReturnCore? storageNames returnTys expr with
      | some coreStmt => some coreStmt
      | none => Stmt.toCore? storageNames (Stmt.returnValues (some expr))
  | Stmt.returnValues
      (some expr@(Expr.callWithOptions (Expr.member _ _) _ _)) =>
      match Expr.externalCallReturnCore? storageNames returnTys expr with
      | some coreStmt => some coreStmt
      | none => Stmt.toCore? storageNames (Stmt.returnValues (some expr))
  | Stmt.returnValues (some (Expr.call (Expr.ident name) args)) =>
      match FunctionDecl.internalSingleReturnCallCore?
          internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
          name args
          (fun retExpr =>
            SolidCore.Solidity.Source.Stmt.returnValues [retExpr]) with
      | some coreStmt => some coreStmt
      | none => Stmt.toCore? storageNames
          (Stmt.returnValues
            (some (Expr.call (Expr.ident name) args)))
  | Stmt.ifElse cond thenBranch elseBranch => do
      let condCore ← Expr.toCore? storageNames cond
      let thenCore ←
        Stmt.toCoreWithInternalCalls?
          (internalFuel := internalFuel)
          (storageRefEnv := storageRefEnv)
          (env := env)
          (storageNames := storageNames)
          (modifiers := modifiers)
          (functions := functions)
          (freeFunctions := freeFunctions)
          (returnTys := returnTys)
          (stmt := thenBranch)
      let elseCore ←
        match elseBranch with
        | some stmt =>
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := env)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := stmt)
        | none => some SolidCore.Solidity.Source.Stmt.skip
      some (SolidCore.Solidity.Source.Stmt.ifElse
        condCore thenCore elseCore)
  | Stmt.whileLoop cond body => do
      let condCore ← Expr.toCore? storageNames cond
      let bodyCore ←
        Stmt.toCoreWithInternalCalls?
          (internalFuel := internalFuel)
          (storageRefEnv := storageRefEnv)
          (env := env)
          (storageNames := storageNames)
          (modifiers := modifiers)
          (functions := functions)
          (freeFunctions := freeFunctions)
          (returnTys := returnTys)
          (stmt := body)
      some (SolidCore.Solidity.Source.Stmt.whileLoop condCore bodyCore)
  | Stmt.doWhile body cond => do
      let bodyCore ←
        Stmt.toCoreWithInternalCalls?
          (internalFuel := internalFuel)
          (storageRefEnv := storageRefEnv)
          (env := env)
          (storageNames := storageNames)
          (modifiers := modifiers)
          (functions := functions)
          (freeFunctions := freeFunctions)
          (returnTys := returnTys)
          (stmt := body)
      let condCore ← Expr.toCore? storageNames cond
      some (SolidCore.Solidity.Source.Stmt.doWhile bodyCore condCore)
  | Stmt.forLoop init cond post body => do
      let initCore ←
        match init with
        | some stmt =>
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := env)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := stmt)
        | none => some SolidCore.Solidity.Source.Stmt.skip
      let condCore ←
        match cond with
        | some expr => Expr.toCore? storageNames expr
        | none => some (SolidCore.Solidity.Source.Expr.word 1)
      let postCore ←
        match post with
        | some expr => Stmt.toCore? storageNames (Stmt.expr expr)
        | none => some SolidCore.Solidity.Source.Stmt.skip
      let bodyCore ←
        Stmt.toCoreWithInternalCalls?
          (internalFuel := internalFuel)
          (storageRefEnv := storageRefEnv)
          (env := env)
          (storageNames := storageNames)
          (modifiers := modifiers)
          (functions := functions)
          (freeFunctions := freeFunctions)
          (returnTys := returnTys)
          (stmt := body)
      some (SolidCore.Solidity.Source.Stmt.forLoop
        initCore condCore postCore bodyCore)
  | Stmt.tryCatch expr clauses => do
      match Expr.toExternalCall? storageNames expr with
      | some (targetCore, calldataCore, valueCore) => do
          let catchCore ←
            CatchClause.listToCoreWithInternalCalls?
              internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
              returnTys clauses
          some
            (SolidCore.Solidity.Source.Stmt.tryExternalCall
              targetCore calldataCore valueCore []
              SolidCore.Solidity.Source.Stmt.skip catchCore)
      | none => do
          let (contractName, argsCore, valueCore, saltCore?) ←
            Expr.toContractCreation? storageNames expr
          let catchCore ←
            CatchClause.listToCoreWithInternalCalls?
              internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
              returnTys clauses
          some
            (SolidCore.Solidity.Source.Stmt.tryContractCreate
              contractName argsCore valueCore saltCore? []
              SolidCore.Solidity.Source.Stmt.skip catchCore)
  | Stmt.tryCatchReturns expr returns success clauses => do
      let returnBindings ← Parameters.toCoreTryBindings? "_try" returns
      let successEnv := Parameters.extendTypeEnv "_try" env returns
      match Expr.toExternalCall? storageNames expr with
      | some (targetCore, calldataCore, valueCore) => do
          let successCore ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := successEnv)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := success)
          let catchCore ←
            CatchClause.listToCoreWithInternalCalls?
              internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
              returnTys clauses
          some
            (SolidCore.Solidity.Source.Stmt.tryExternalCall
              targetCore calldataCore valueCore returnBindings successCore
              catchCore)
      | none => do
          let (contractName, argsCore, valueCore, saltCore?) ←
            Expr.toContractCreation? storageNames expr
          let successCore ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := successEnv)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := success)
          let catchCore ←
            CatchClause.listToCoreWithInternalCalls?
              internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
              returnTys clauses
          some
            (SolidCore.Solidity.Source.Stmt.tryContractCreate
              contractName argsCore valueCore saltCore? returnBindings
              successCore catchCore)
  | Stmt.unchecked body => do
      let bodyCore ←
        Stmt.toCoreWithInternalCalls?
          (internalFuel := internalFuel)
          (storageRefEnv := storageRefEnv)
          (env := env)
          (storageNames := storageNames)
          (modifiers := modifiers)
          (functions := functions)
          (freeFunctions := freeFunctions)
          (returnTys := returnTys)
          (stmt := body)
      some (SolidCore.Solidity.Source.Stmt.unchecked bodyCore)
  | other => Stmt.toCore? storageNames other
termination_by (internalFuel, sizeOf stmt, 5)

def Stmt.listToCoreWithInternalCallsWithRefs?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions : List FunctionDecl) (freeFunctions : List FunctionDecl)
    (returnTys : List Ty) (stmts : List Stmt) :
    Option (List CoreStmt) :=
  match stmts with
  | [] => some []
  | Stmt.expr (Expr.assign (Expr.ident name) AssignOp.assign
      (Expr.ident target)) :: rest =>
      match storageAliasAssignmentCore? storageRefEnv storageNames name target with
      | some head => do
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              storageRefEnv env storageNames modifiers functions
              freeFunctions returnTys rest
          some (head :: tail)
      | none => do
          let head ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := env)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := Stmt.expr
                (Expr.assign (Expr.ident name) AssignOp.assign
                  (Expr.ident target)))
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              storageRefEnv env storageNames modifiers functions
              freeFunctions returnTys rest
          some (head :: tail)
  | Stmt.varDecl [binding] (some (Expr.ident source)) :: rest =>
      match storageAliasDeclFromRefCore? storageRefEnv binding source with
      | some head => do
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              (VarBinding.extendStorageRefEnv storageRefEnv binding)
              (VarBinding.extendTypeEnv env binding)
              storageNames modifiers functions freeFunctions returnTys rest
          some (head :: tail)
      | none => do
          let head ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := env)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := Stmt.varDecl [binding] (some (Expr.ident source)))
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              (VarBinding.extendStorageRefEnv storageRefEnv binding)
              (VarBinding.extendTypeEnv env binding)
              storageNames modifiers functions freeFunctions returnTys rest
          some (head :: tail)
  | Stmt.varDecl bindings@(_ :: _ :: _) (some (Expr.tuple items)) :: rest => do
      let (coreDecls, assigns) ←
        tupleVarDeclCorePieces? storageNames bindings items
      let tail ←
        Stmt.listToCoreWithInternalCallsWithRefs?
          internalFuel
          (VarBindings.extendStorageRefEnv storageRefEnv bindings)
          (VarBindings.extendTypeEnv env bindings)
          storageNames modifiers functions freeFunctions returnTys rest
      some (coreDecls ++ assigns ++ tail)
  | Stmt.varDecl [binding] (some expr@(Expr.call (Expr.member _ _) _)) :: rest =>
      match binding.name, binding.ty with
      | some localName, some expectedTy =>
          match Expr.externalCallSingleReturnCore?
              storageNames expectedTy expr
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.assign
                  (SolidCore.Solidity.Source.LValue.var localName)
                  retExpr) with
          | some assignBlock => do
              let declCore ←
                Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  storageNames modifiers functions freeFunctions returnTys rest
              some (declCore :: assignBlock :: tail)
          | none => do
              let head ←
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := Stmt.varDecl [binding] (some expr))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | _, _ => do
          let head ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := env)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := Stmt.varDecl [binding] (some expr))
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              (VarBinding.extendStorageRefEnv storageRefEnv binding)
              (VarBinding.extendTypeEnv env binding)
              storageNames modifiers functions freeFunctions returnTys rest
          some (head :: tail)
  | Stmt.varDecl [binding]
      (some expr@(Expr.callWithOptions (Expr.member _ _) _ _)) :: rest =>
      match binding.name, binding.ty with
      | some localName, some expectedTy =>
          match Expr.externalCallSingleReturnCore?
              storageNames expectedTy expr
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.assign
                  (SolidCore.Solidity.Source.LValue.var localName)
                  retExpr) with
          | some assignBlock => do
              let declCore ←
                Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  storageNames modifiers functions freeFunctions returnTys rest
              some (declCore :: assignBlock :: tail)
          | none => do
              let head ←
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := Stmt.varDecl [binding] (some expr))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | _, _ => do
          let head ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := env)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := Stmt.varDecl [binding] (some expr))
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              (VarBinding.extendStorageRefEnv storageRefEnv binding)
              (VarBinding.extendTypeEnv env binding)
              storageNames modifiers functions freeFunctions returnTys rest
          some (head :: tail)
  | Stmt.varDecl [binding] (some (Expr.call (Expr.ident name) args)) :: rest =>
      match binding.name with
      | some localName =>
          match FunctionDecl.internalSingleReturnCallCore?
              internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
              name args
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.assign
                  (SolidCore.Solidity.Source.LValue.var localName)
                  retExpr) with
          | some assignBlock => do
              let declCore ←
                Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  storageNames modifiers functions freeFunctions returnTys rest
              some (declCore :: assignBlock :: tail)
          | none => do
              let head ←
                Stmt.toCore? storageNames
                  (Stmt.varDecl [binding]
                    (some (Expr.call (Expr.ident name) args)))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | none => do
          let head ←
            Stmt.toCore? storageNames
              (Stmt.varDecl [binding]
                (some (Expr.call (Expr.ident name) args)))
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              (VarBinding.extendStorageRefEnv storageRefEnv binding)
              (VarBinding.extendTypeEnv env binding)
              storageNames modifiers functions freeFunctions returnTys rest
          some (head :: tail)
  | Stmt.varDecl bindings (some expr@(Expr.call (Expr.member _ _) _)) :: rest => do
      let names ← VarBindings.names? bindings
      let callReturnTys ← VarBindings.sourceTys? bindings
      let decls ← VarBindings.toCoreDecls? bindings
      let callCore ←
        Expr.externalCallAssignVarsCore?
          storageNames callReturnTys names expr
      let tail ←
        Stmt.listToCoreWithInternalCallsWithRefs?
          internalFuel
          (VarBindings.extendStorageRefEnv storageRefEnv bindings)
          (VarBindings.extendTypeEnv env bindings)
          storageNames modifiers functions freeFunctions returnTys rest
      some (decls ++ [callCore] ++ tail)
  | Stmt.varDecl bindings
      (some expr@(Expr.callWithOptions (Expr.member _ _) _ _)) :: rest => do
      let names ← VarBindings.names? bindings
      let callReturnTys ← VarBindings.sourceTys? bindings
      let decls ← VarBindings.toCoreDecls? bindings
      let callCore ←
        Expr.externalCallAssignVarsCore?
          storageNames callReturnTys names expr
      let tail ←
        Stmt.listToCoreWithInternalCallsWithRefs?
          internalFuel
          (VarBindings.extendStorageRefEnv storageRefEnv bindings)
          (VarBindings.extendTypeEnv env bindings)
          storageNames modifiers functions freeFunctions returnTys rest
      some (decls ++ [callCore] ++ tail)
  | Stmt.varDecl bindings (some (Expr.call (Expr.ident name) args)) :: rest => do
      let names ← VarBindings.names? bindings
      let decls ← VarBindings.toCoreDecls? bindings
      let callCore ←
        FunctionDecl.internalAssignReturnCallCore?
          internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
          name args names
      let tail ←
        Stmt.listToCoreWithInternalCallsWithRefs?
          internalFuel
          (VarBindings.extendStorageRefEnv storageRefEnv bindings)
          (VarBindings.extendTypeEnv env bindings)
          storageNames modifiers functions freeFunctions returnTys rest
      some (decls ++ [callCore] ++ tail)
  | stmt :: rest => do
      let head ←
        Stmt.toCoreWithInternalCalls?
          (internalFuel := internalFuel)
          (storageRefEnv := storageRefEnv)
          (env := env)
          (storageNames := storageNames)
          (modifiers := modifiers)
          (functions := functions)
          (freeFunctions := freeFunctions)
          (returnTys := returnTys)
          (stmt := stmt)
      let nextEnv :=
        match stmt with
        | Stmt.varDecl bindings _ => VarBindings.extendTypeEnv env bindings
        | _ => env
      let nextStorageRefEnv :=
        match stmt with
        | Stmt.varDecl bindings _ =>
            VarBindings.extendStorageRefEnv storageRefEnv bindings
        | _ => storageRefEnv
      let tail ←
        Stmt.listToCoreWithInternalCallsWithRefs?
          internalFuel
          nextStorageRefEnv nextEnv storageNames modifiers functions
          freeFunctions returnTys rest
      some (head :: tail)
termination_by (internalFuel, sizeOf stmts, 4)

def CatchClause.toCoreWithInternalCalls? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (clause : CatchClause) : Option CoreTryCatchClause :=
  match clause with
  | CatchClause.clause name params body => do
      let bindings ← Parameters.toCoreTryBindings? "_catch" params
      let catchEnv := Parameters.extendTypeEnv "_catch" env params
      let bodyCore ←
        Stmt.toCoreWithInternalCalls?
          (internalFuel := internalFuel)
          (storageRefEnv := storageRefEnv)
          (env := catchEnv)
          (storageNames := storageNames)
          (modifiers := modifiers)
          (functions := functions)
          (freeFunctions := freeFunctions)
          (returnTys := returnTys)
          (stmt := body)
      some (SolidCore.Solidity.Source.TryCatchClause.clause
        name bindings bodyCore)
termination_by (internalFuel, sizeOf clause, 3)

def CatchClause.listToCoreWithInternalCalls? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (clauses : List CatchClause) : Option (List CoreTryCatchClause) :=
  match clauses with
  | [] => some []
  | clause :: rest => do
      let head ←
        CatchClause.toCoreWithInternalCalls?
          internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
          returnTys clause
      let tail ←
        CatchClause.listToCoreWithInternalCalls?
          internalFuel storageRefEnv env storageNames modifiers functions freeFunctions
          returnTys rest
      some (head :: tail)
termination_by (internalFuel, sizeOf clauses, 4)

end

def Stmt.listToCoreWithInternalCalls? (env : TypeEnv) (storageNames : List Name)
    (modifiers : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl) (returnTys : List Ty) (stmts : List Stmt) :
    Option (List CoreStmt) :=
  Stmt.listToCoreWithInternalCallsWithRefs?
    defaultInternalCallInlineFuel [] env storageNames modifiers functions
    freeFunctions returnTys stmts

def defaultModifierPlaceholderReplacementFuel : Nat := 1024

mutual

def Stmt.containsModifierPlaceholder : Stmt -> Bool
  | Stmt.modifierPlaceholder => true
  | Stmt.block body => Stmt.listContainsModifierPlaceholder body
  | Stmt.ifElse _ thenBranch elseBranch =>
      Stmt.containsModifierPlaceholder thenBranch ||
        match elseBranch with
        | some stmt => Stmt.containsModifierPlaceholder stmt
        | none => false
  | Stmt.whileLoop _ body => Stmt.containsModifierPlaceholder body
  | Stmt.doWhile body _ => Stmt.containsModifierPlaceholder body
  | Stmt.forLoop init _ _ body =>
      (match init with
        | some stmt => Stmt.containsModifierPlaceholder stmt
        | none => false) ||
        Stmt.containsModifierPlaceholder body
  | Stmt.tryCatch _ clauses =>
      CatchClause.listContainsModifierPlaceholder clauses
  | Stmt.tryCatchReturns _ _ success clauses =>
      Stmt.containsModifierPlaceholder success ||
        CatchClause.listContainsModifierPlaceholder clauses
  | Stmt.unchecked body => Stmt.containsModifierPlaceholder body
  | _ => false

def CatchClause.containsModifierPlaceholder : CatchClause -> Bool
  | CatchClause.clause _ _ body => Stmt.containsModifierPlaceholder body

def CatchClause.listContainsModifierPlaceholder : List CatchClause -> Bool
  | [] => false
  | clause :: rest =>
      CatchClause.containsModifierPlaceholder clause ||
        CatchClause.listContainsModifierPlaceholder rest

def Stmt.listContainsModifierPlaceholder : List Stmt -> Bool
  | [] => false
  | stmt :: rest =>
      Stmt.containsModifierPlaceholder stmt ||
        Stmt.listContainsModifierPlaceholder rest

end

mutual

def Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
    (replaceFuel internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (returnNames : List Name) (replacement : CoreStmt) (stmt : Stmt) :
    Option CoreStmt :=
  match replaceFuel with
  | 0 => none
  | replaceFuel + 1 =>
      match stmt with
      | Stmt.modifierPlaceholder =>
          some (SolidCore.Solidity.Source.Stmt.captureReturn
            returnNames replacement)
      | Stmt.block body => do
          let coreBody ←
            Stmt.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement body
          some (SolidCore.Solidity.Source.Stmt.block coreBody)
      | Stmt.ifElse cond thenBranch elseBranch => do
          let condCore ← Expr.toCore? storageNames cond
          let thenCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement thenBranch
          let elseCore ←
            match elseBranch with
            | some stmt =>
                Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
                  replaceFuel internalFuel storageRefEnv env storageNames
                  modifiers functions freeFunctions returnTys returnNames
                  replacement stmt
            | none => some SolidCore.Solidity.Source.Stmt.skip
          some (SolidCore.Solidity.Source.Stmt.ifElse
            condCore thenCore elseCore)
      | Stmt.whileLoop cond body => do
          let condCore ← Expr.toCore? storageNames cond
          let bodyCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement body
          some (SolidCore.Solidity.Source.Stmt.whileLoop condCore bodyCore)
      | Stmt.doWhile body cond => do
          let bodyCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement body
          let condCore ← Expr.toCore? storageNames cond
          some (SolidCore.Solidity.Source.Stmt.doWhile bodyCore condCore)
      | Stmt.forLoop init cond post body => do
          let initCore ←
            match init with
            | some stmt =>
                Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
                  replaceFuel internalFuel storageRefEnv env storageNames
                  modifiers functions freeFunctions returnTys returnNames
                  replacement stmt
            | none => some SolidCore.Solidity.Source.Stmt.skip
          let condCore ←
            match cond with
            | some expr => Expr.toCore? storageNames expr
            | none => some (SolidCore.Solidity.Source.Expr.word 1)
          let postCore ←
            match post with
            | some expr => Stmt.toCore? storageNames (Stmt.expr expr)
            | none => some SolidCore.Solidity.Source.Stmt.skip
          let bodyCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement body
          some (SolidCore.Solidity.Source.Stmt.forLoop
            initCore condCore postCore bodyCore)
      | Stmt.tryCatch expr clauses => do
          let catchCore ←
            CatchClause.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env storageNames modifiers
              functions freeFunctions returnTys returnNames replacement clauses
          match Expr.toExternalCall? storageNames expr with
          | some (targetCore, calldataCore, valueCore) =>
              some
                (SolidCore.Solidity.Source.Stmt.tryExternalCall
                  targetCore calldataCore valueCore []
                  SolidCore.Solidity.Source.Stmt.skip catchCore)
          | none => do
              let (contractName, argsCore, valueCore, saltCore?) ←
                Expr.toContractCreation? storageNames expr
              some
                (SolidCore.Solidity.Source.Stmt.tryContractCreate
                  contractName argsCore valueCore saltCore? []
                  SolidCore.Solidity.Source.Stmt.skip catchCore)
      | Stmt.tryCatchReturns expr returns success clauses => do
          let returnBindings ← Parameters.toCoreTryBindings? "_try" returns
          let successEnv := Parameters.extendTypeEnv "_try" env returns
          let successCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv successEnv storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement success
          let catchCore ←
            CatchClause.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env storageNames modifiers
              functions freeFunctions returnTys returnNames replacement clauses
          match Expr.toExternalCall? storageNames expr with
          | some (targetCore, calldataCore, valueCore) =>
              some
                (SolidCore.Solidity.Source.Stmt.tryExternalCall
                  targetCore calldataCore valueCore returnBindings
                  successCore catchCore)
          | none => do
              let (contractName, argsCore, valueCore, saltCore?) ←
                Expr.toContractCreation? storageNames expr
              some
                (SolidCore.Solidity.Source.Stmt.tryContractCreate
                  contractName argsCore valueCore saltCore? returnBindings
                  successCore catchCore)
      | Stmt.unchecked body => do
          let bodyCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement body
          some (SolidCore.Solidity.Source.Stmt.unchecked bodyCore)
      | other =>
          Stmt.toCoreWithInternalCalls?
            (internalFuel := internalFuel)
            (storageRefEnv := storageRefEnv)
            (env := env)
            (storageNames := storageNames)
            (modifiers := modifiers)
            (functions := functions)
            (freeFunctions := freeFunctions)
            (returnTys := returnTys)
            (stmt := other)

def CatchClause.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
    (replaceFuel internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (returnNames : List Name) (replacement : CoreStmt)
    (clause : CatchClause) : Option CoreTryCatchClause :=
  match replaceFuel with
  | 0 => none
  | replaceFuel + 1 =>
      match clause with
      | CatchClause.clause name params body => do
          let bindings ← Parameters.toCoreTryBindings? "_catch" params
          let catchEnv := Parameters.extendTypeEnv "_catch" env params
          let bodyCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv catchEnv storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement body
          some
            (SolidCore.Solidity.Source.TryCatchClause.clause
              name bindings bodyCore)

def CatchClause.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
    (replaceFuel internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (returnNames : List Name) (replacement : CoreStmt)
    (clauses : List CatchClause) : Option (List CoreTryCatchClause) :=
  match replaceFuel with
  | 0 => none
  | replaceFuel + 1 =>
      match clauses with
      | [] => some []
      | clause :: rest => do
          let head ←
            CatchClause.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env storageNames modifiers
              functions freeFunctions returnTys returnNames replacement clause
          let tail ←
            CatchClause.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env storageNames modifiers
              functions freeFunctions returnTys returnNames replacement rest
          some (head :: tail)

def Stmt.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
    (replaceFuel internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (returnNames : List Name) (replacement : CoreStmt)
    (stmts : List Stmt) : Option (List CoreStmt) :=
  match replaceFuel with
  | 0 => none
  | replaceFuel + 1 =>
      match stmts with
      | [] => some []
      | stmt :: rest => do
          let head ←
            if Stmt.containsModifierPlaceholder stmt then
              do
                let coreStmt ←
                  Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
                    replaceFuel internalFuel storageRefEnv env storageNames
                    modifiers functions freeFunctions returnTys returnNames
                    replacement stmt
                some [coreStmt]
            else
              Stmt.listToCoreWithInternalCallsWithRefs?
                internalFuel storageRefEnv env storageNames modifiers
                functions freeFunctions returnTys [stmt]
          let nextEnv :=
            match stmt with
            | Stmt.varDecl bindings _ => VarBindings.extendTypeEnv env bindings
            | _ => env
          let nextStorageRefEnv :=
            match stmt with
            | Stmt.varDecl bindings _ =>
                VarBindings.extendStorageRefEnv storageRefEnv bindings
            | _ => storageRefEnv
          let tail ←
            Stmt.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel nextStorageRefEnv nextEnv storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement rest
          some (head ++ tail)

end

def Stmt.toCoreWithInternalCallsReplacingModifierPlaceholder?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (returnNames : List Name) (replacement : CoreStmt) (stmt : Stmt) :
    Option CoreStmt :=
  Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
    defaultModifierPlaceholderReplacementFuel internalFuel storageRefEnv env
    storageNames modifiers functions freeFunctions returnTys returnNames
    replacement stmt

def modifierApplyToCoreWithInternalCalls? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames returnNames : List Name)
    (available : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (decl : SourceModifierDecl)
    (invocation : SourceModifierInvocation) (inner : CoreStmt) :
    Option CoreStmt := do
  let body ← decl.body
  let prefixStmts ← modifierParamBindingsWithArgs? decl invocation.args
  let prefixCore ←
    Stmt.listToCoreWithInternalCallsWithRefs?
      internalFuel storageRefEnv env storageNames available functions
      freeFunctions returnTys prefixStmts
  let modifierEnv := Parameters.extendTypeEnv "_mod" env decl.params
  let modifierStorageRefEnv :=
    Parameters.extendStorageRefEnv "_mod" storageRefEnv decl.params
  let body := Stmt.annotateAbi modifierEnv body
  let bodyCore ←
    Stmt.toCoreWithInternalCallsReplacingModifierPlaceholder?
      internalFuel modifierStorageRefEnv modifierEnv storageNames
      available functions freeFunctions returnTys returnNames inner body
  some (SolidCore.Solidity.Source.Stmt.block (prefixCore ++ [bodyCore]))

def functionExpandModifiersToCoreWithInternalCallsFull?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (storageNames returnNames : List Name)
    (available : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (invocations : List SourceModifierInvocation) (body : Stmt) :
    Option CoreStmt :=
  match invocations with
  | [] =>
      Stmt.toCoreWithInternalCalls?
        (internalFuel := internalFuel)
        (storageRefEnv := storageRefEnv)
        (env := env)
        (storageNames := storageNames)
        (modifiers := available)
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := body)
  | invocation :: rest => do
      let inner ←
        functionExpandModifiersToCoreWithInternalCallsFull?
          internalFuel storageRefEnv env storageNames returnNames available
          functions freeFunctions returnTys rest body
      let modifierName ← pathLast? invocation.target
      let modifierDecl ← modifierFindByName? available modifierName
      modifierApplyToCoreWithInternalCalls? internalFuel storageRefEnv env
        storageNames returnNames available functions freeFunctions returnTys
        modifierDecl invocation inner
termination_by invocations.length

def libraryHelperName (libraryName functionName : Name) : Name :=
  "__library_" ++ libraryName ++ "_" ++ functionName

def ContractDecl.isLibrary (decl : ContractDecl) : Bool :=
  match decl.kind with
  | ContractKind.library => true
  | _ => false

def ContractDecls.hasLibrary : List ContractDecl -> Bool
  | [] => false
  | decl :: rest =>
      ContractDecl.isLibrary decl || ContractDecls.hasLibrary rest

def ContractDecl.findLibraryByName? (contracts : List ContractDecl)
    (name : Name) : Option ContractDecl :=
  contracts.find? (fun decl => decl.name == name && ContractDecl.isLibrary decl)

def FunctionDecl.isInlineLibraryFunction (decl : FunctionDecl) : Bool :=
  match decl.visibility with
  | some Visibility.public_ | some Visibility.external_ => false
  | _ => !FunctionDecl.isConstructor decl

def ContractItems.findOrdinaryFunctionByName?
    (items : List ContractItem) (name : Name) : Option FunctionDecl :=
  match items with
  | [] => none
  | ContractItem.function fn :: rest =>
      if FunctionDecl.isInlineLibraryFunction fn then
        match fn.name with
        | some fnName =>
            if fnName == name then
              some fn
            else
              ContractItems.findOrdinaryFunctionByName? rest name
        | none =>
            ContractItems.findOrdinaryFunctionByName? rest name
      else
        ContractItems.findOrdinaryFunctionByName? rest name
  | _ :: rest =>
      ContractItems.findOrdinaryFunctionByName? rest name
termination_by items.length

def ContractDecl.findOrdinaryFunctionByName? (decl : ContractDecl)
    (name : Name) : Option FunctionDecl :=
  ContractItems.findOrdinaryFunctionByName? decl.items name

def FunctionDecl.firstParamMatches? (env : TypeEnv)
    (receiver : Expr) (decl : FunctionDecl) : Option Bool := do
  match decl.params with
  | first :: _ =>
      let receiverTy ← Expr.abiTyWithEnv? env receiver
      some (Ty.matchesShape receiverTy first.ty)
  | [] => some false

def UsingDecl.targetMatches? (env : TypeEnv)
    (receiver : Expr) (decl : UsingDecl) : Option Bool :=
  match decl.target with
  | some targetTy => do
      let receiverTy ← Expr.abiTyWithEnv? env receiver
      some (Ty.matchesShape receiverTy targetTy)
  | none => some true

def UsingDecl.rewriteCall? (contracts : List ContractDecl)
    (env : TypeEnv) (receiver : Expr) (method : Name)
    (args : List Arg) (decl : UsingDecl) : Option Expr := do
  let receiverMatches ← UsingDecl.targetMatches? env receiver decl
  if !receiverMatches then
    none
  else
    some ()
  let libraryName ← pathLast? decl.library
  let libraryDecl ← ContractDecl.findLibraryByName? contracts libraryName
  let fn ← ContractDecl.findOrdinaryFunctionByName? libraryDecl method
  let firstMatches ← FunctionDecl.firstParamMatches? env receiver fn
  if firstMatches then
    some ()
  else
    none
  let orderedArgs ← Args.toExprsForParams? (fn.params.drop 1) args
  match Parameters.matchArgsWithEnv? env fn.params (receiver :: orderedArgs) with
  | some true =>
      some
        (Expr.call (Expr.ident (libraryHelperName libraryName method))
          ((receiver :: orderedArgs).map Arg.positional))
  | _ => none

def UsingDecls.rewriteCall? (contracts : List ContractDecl)
    (env : TypeEnv) (receiver : Expr) (method : Name)
    (args : List Arg) : List UsingDecl -> Option Expr
  | [] => none
  | decl :: rest =>
      match
          UsingDecl.rewriteCall?
            contracts env receiver method args decl with
      | some rewritten => some rewritten
      | none => UsingDecls.rewriteCall? contracts env receiver method args rest

def libraryDirectCallRewrite? (contracts : List ContractDecl)
    (env : TypeEnv) (receiver : Expr) (method : Name)
    (args : List Arg) : Option Expr := do
  let libraryName ←
    match receiver with
    | Expr.ident name => some name
    | _ => none
  let libraryDecl ← ContractDecl.findLibraryByName? contracts libraryName
  let fn ← ContractDecl.findOrdinaryFunctionByName? libraryDecl method
  let orderedArgs ← Args.toExprsForParams? fn.params args
  match Parameters.matchArgsWithEnv? env fn.params orderedArgs with
  | some true =>
      some
        (Expr.call (Expr.ident (libraryHelperName libraryName method))
          (orderedArgs.map Arg.positional))
  | _ => none

mutual

def Expr.expandUsingFuel :
    Nat -> List ContractDecl -> List UsingDecl -> TypeEnv -> Expr -> Expr
  | 0, _, _, _, expr => expr
  | fuel + 1, contracts, usingDecls, env, expr =>
      let expand := Expr.expandUsingFuel fuel contracts usingDecls env
      let expandArg := Arg.expandUsingFuel fuel contracts usingDecls env
      let expandOption := CallOption.expandUsingFuel fuel contracts usingDecls env
      let expandTupleItem :=
        TupleItem.expandUsingFuel fuel contracts usingDecls env
      match expr with
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (expand base) member
      | Expr.index base index => Expr.index (expand base) (expand index)
      | Expr.slice base start stop =>
          Expr.slice (expand base) (start.map expand) (stop.map expand)
      | Expr.call (Expr.member receiver method) args =>
          let receiver' := expand receiver
          let args' := args.map expandArg
          match libraryDirectCallRewrite? contracts env receiver' method args' with
          | some rewritten => rewritten
          | none =>
              match UsingDecls.rewriteCall?
                  contracts env receiver' method args' usingDecls with
              | some rewritten => rewritten
              | none => Expr.call (Expr.member receiver' method) args'
      | Expr.call fn args =>
          Expr.call (expand fn) (args.map expandArg)
      | Expr.callWithOptions (Expr.member receiver method) options args =>
          let receiver' := expand receiver
          let options' := options.map expandOption
          let args' := args.map expandArg
          match libraryDirectCallRewrite? contracts env receiver' method args' with
          | some rewritten =>
              match rewritten with
              | Expr.call fn args => Expr.callWithOptions fn options' args
              | other => other
          | none =>
              match UsingDecls.rewriteCall?
                  contracts env receiver' method args' usingDecls with
              | some rewritten =>
                  match rewritten with
                  | Expr.call fn args => Expr.callWithOptions fn options' args
                  | other => other
              | none =>
                  Expr.callWithOptions
                    (Expr.member receiver' method) options' args'
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (expand fn)
            (options.map expandOption) (args.map expandArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map expandArg)
      | Expr.tuple items => Expr.tuple (items.map expandTupleItem)
      | Expr.array exprs => Expr.array (exprs.map expand)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (expand inner)
      | Expr.unary op inner => Expr.unary op (expand inner)
      | Expr.binary op lhs rhs => Expr.binary op (expand lhs) (expand rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (expand cond) (expand thenExpr) (expand elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (expand lhs) op (expand rhs)
      | Expr.payableConversion inner => Expr.payableConversion (expand inner)

def Arg.expandUsingFuel :
    Nat -> List ContractDecl -> List UsingDecl -> TypeEnv -> Arg -> Arg
  | 0, _, _, _, arg => arg
  | fuel + 1, contracts, usingDecls, env, arg =>
      let expand := Expr.expandUsingFuel fuel contracts usingDecls env
      match arg with
      | Arg.positional expr => Arg.positional (expand expr)
      | Arg.named name expr => Arg.named name (expand expr)

def CallOption.expandUsingFuel :
    Nat -> List ContractDecl -> List UsingDecl -> TypeEnv -> CallOption ->
    CallOption
  | 0, _, _, _, option => option
  | fuel + 1, contracts, usingDecls, env, option =>
      let expand := Expr.expandUsingFuel fuel contracts usingDecls env
      match option with
      | CallOption.named name expr => CallOption.named name (expand expr)

def TupleItem.expandUsingFuel :
    Nat -> List ContractDecl -> List UsingDecl -> TypeEnv -> TupleItem ->
    TupleItem
  | 0, _, _, _, item => item
  | fuel + 1, contracts, usingDecls, env, item =>
      let expand := Expr.expandUsingFuel fuel contracts usingDecls env
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (expand expr)

end

def defaultExpandUsingFuel : Nat := 1024

def Expr.expandUsing (contracts : List ContractDecl)
    (usingDecls : List UsingDecl) (env : TypeEnv) (expr : Expr) : Expr :=
  Expr.expandUsingFuel defaultExpandUsingFuel contracts usingDecls env expr

def Arg.expandUsing (contracts : List ContractDecl)
    (usingDecls : List UsingDecl) (env : TypeEnv) (arg : Arg) : Arg :=
  Arg.expandUsingFuel defaultExpandUsingFuel contracts usingDecls env arg

def ModifierInvocation.expandUsing (contracts : List ContractDecl)
    (usingDecls : List UsingDecl) (env : TypeEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with
    args := invocation.args.map (Arg.expandUsing contracts usingDecls env) }

def Stmt.expandUsingInSeqFuel :
    Nat -> List ContractDecl -> List UsingDecl -> TypeEnv -> Stmt ->
    Stmt × TypeEnv
  | 0, _, _, env, stmt => (stmt, env)
  | fuel + 1, contracts, usingDecls, env, stmt =>
      let expandExpr := Expr.expandUsingFuel fuel contracts usingDecls env
      let expandStmt (child : Stmt) :=
        (Stmt.expandUsingInSeqFuel fuel contracts usingDecls env child).fst
      let expandSeq (seqEnv : TypeEnv) (body : List Stmt) :
          List Stmt × TypeEnv :=
        let step (acc : List Stmt × TypeEnv) (head : Stmt) :
            List Stmt × TypeEnv :=
          let (done, seqEnv) := acc
          let (head', seqEnv') :=
            Stmt.expandUsingInSeqFuel fuel contracts usingDecls seqEnv head
          (head' :: done, seqEnv')
        let (revBody, finalEnv) :=
          body.foldl step (([] : List Stmt), seqEnv)
        (revBody.reverse, finalEnv)
      let expandClause : CatchClause -> CatchClause
        | CatchClause.clause name params body =>
            let clauseEnv := Parameters.extendTypeEnv "_catch" env params
            CatchClause.clause name params
              ((Stmt.expandUsingInSeqFuel
                fuel contracts usingDecls clauseEnv body).fst)
      match stmt with
      | Stmt.empty => (Stmt.empty, env)
      | Stmt.block body =>
          let (body', _) := expandSeq env body
          (Stmt.block body', env)
      | Stmt.varDecl bindings init =>
          let init' := init.map expandExpr
          let env' := VarBindings.extendTypeEnv env bindings
          (Stmt.varDecl bindings init', env')
      | Stmt.expr expr => (Stmt.expr (expandExpr expr), env)
      | Stmt.ifElse cond thenBranch elseBranch =>
          (Stmt.ifElse (expandExpr cond) (expandStmt thenBranch)
            (elseBranch.map expandStmt), env)
      | Stmt.whileLoop cond body =>
          (Stmt.whileLoop (expandExpr cond) (expandStmt body), env)
      | Stmt.doWhile body cond =>
          (Stmt.doWhile (expandStmt body) (expandExpr cond), env)
      | Stmt.forLoop init cond post body =>
          let (init', loopEnv) :=
            match init with
            | some initStmt =>
                let (stmt', env') :=
                  Stmt.expandUsingInSeqFuel
                    fuel contracts usingDecls env initStmt
                (some stmt', env')
            | none => (none, env)
          let expandLoopExpr :=
            Expr.expandUsingFuel fuel contracts usingDecls loopEnv
          let body' :=
            (Stmt.expandUsingInSeqFuel
              fuel contracts usingDecls loopEnv body).fst
          (Stmt.forLoop init' (cond.map expandLoopExpr)
            (post.map expandLoopExpr) body', env)
      | Stmt.tryCatch expr clauses =>
          (Stmt.tryCatch (expandExpr expr) (clauses.map expandClause), env)
      | Stmt.tryCatchReturns expr returns success clauses =>
          let successEnv := Parameters.extendTypeEnv "_try" env returns
          let success' :=
            (Stmt.expandUsingInSeqFuel
              fuel contracts usingDecls successEnv success).fst
          (Stmt.tryCatchReturns (expandExpr expr) returns success'
            (clauses.map expandClause), env)
      | Stmt.emitEvent expr => (Stmt.emitEvent (expandExpr expr), env)
      | Stmt.revertCall expr => (Stmt.revertCall (expandExpr expr), env)
      | Stmt.returnValues expr? =>
          (Stmt.returnValues (expr?.map expandExpr), env)
      | Stmt.break => (Stmt.break, env)
      | Stmt.continue => (Stmt.continue, env)
      | Stmt.unchecked body => (Stmt.unchecked (expandStmt body), env)
      | Stmt.inlineAssembly code => (Stmt.inlineAssembly code, env)
      | Stmt.modifierPlaceholder => (Stmt.modifierPlaceholder, env)

def Stmt.expandUsing (contracts : List ContractDecl)
    (usingDecls : List UsingDecl) (env : TypeEnv) (stmt : Stmt) : Stmt :=
  (Stmt.expandUsingInSeqFuel
    defaultExpandUsingFuel contracts usingDecls env stmt).fst

def ModifierDecl.expandUsing (contracts : List ContractDecl)
    (usingDecls : List UsingDecl) (env : TypeEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  let modifierEnv := Parameters.extendTypeEnv "_mod" env decl.params
  { decl with
    body := decl.body.map
      (fun body => Stmt.expandUsing contracts usingDecls modifierEnv body) }

def FunctionDecl.toCore? (storageNames : List Name) (constants : ConstantEnv)
    (extraEnv : TypeEnv)
    (contracts : List ContractDecl) (usingDecls : List UsingDecl)
    (modifiers : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl)
    (decl : FunctionDecl) (superFunctions : List FunctionDecl := [])
    (contractName? : Option Name := none)
    (baseNames : List Name := []) :
    Option CoreFunctionDef := do
  let decl := FunctionDecl.inlineConstants constants decl
  let selectorEnv :=
    FunctionDecls.selectorEntries (decl :: functions ++ freeFunctions)
  let decl := FunctionDecl.resolveFunctionAddresses selectorEnv decl
  let decl := FunctionDecl.resolveSelectors selectorEnv decl
  let name ← FunctionDecl.coreName? decl
  let params ← Parameters.toCoreBindings? "_arg" decl.params
  let returns ← Parameters.toCoreBindings? "_ret" decl.returns
  let body ← decl.body
  let env := FunctionDecl.typeEnv extraEnv decl
  let body :=
    if usingDecls.isEmpty && !ContractDecls.hasLibrary contracts then
      body
    else
      Stmt.expandUsing contracts usingDecls env body
  let modifiers :=
    if usingDecls.isEmpty && !ContractDecls.hasLibrary contracts then
      modifiers
    else
      modifiers.map (ModifierDecl.expandUsing contracts usingDecls env)
  let modifierInvocations :=
    if usingDecls.isEmpty && !ContractDecls.hasLibrary contracts then
      decl.modifiers
    else
      decl.modifiers.map
        (ModifierInvocation.expandUsing contracts usingDecls env)
  let body :=
    match contractName? with
    | some contractName => Stmt.rewriteSuperCalls contractName body
    | none => body
  let body := Stmt.rewriteBaseCalls baseNames body
  let body := Stmt.annotateAbi env body
  let storageRefEnv := Parameters.extendStorageRefEnv "_arg" [] decl.params
  let functions :=
    match contractName? with
    | some contractName =>
        functions ++ FunctionDecl.superHelpers contractName superFunctions
    | none => functions
  let bodyCore ←
    functionExpandModifiersToCoreWithInternalCallsFull?
      defaultInternalCallInlineFuel storageRefEnv env
      storageNames (returns.map SolidCore.Solidity.Source.BindingDecl.name)
      modifiers functions freeFunctions (decl.returns.map Parameter.ty)
      modifierInvocations body
  some
    { name := name
      selector? := FunctionDecl.abiSelector? decl
      payable := FunctionDecl.isPayable decl
      params := params
      returns := returns
      body := bodyCore }

def FunctionDecl.rewriteDispatchCalls (contractName : Name)
    (baseNames : List Name) (decl : FunctionDecl) : FunctionDecl :=
  { decl with
    body :=
      decl.body.map (fun body =>
        Stmt.rewriteBaseCalls baseNames
          (Stmt.rewriteSuperCalls contractName body)) }

def ContractDecl.directStateVars (decl : ContractDecl) : List StateVarDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.stateVar stateVar => some stateVar
    | _ => none)

def StateVarDecl.isConstant (decl : StateVarDecl) : Bool :=
  match decl.mutability with
  | VarMutability.constant => true
  | _ => false

def StateVarDecl.isImmutable (decl : StateVarDecl) : Bool :=
  match decl.mutability with
  | VarMutability.immutable => true
  | _ => false

def StateVarDecl.isStorageBacked (decl : StateVarDecl) : Bool :=
  match decl.mutability with
  | VarMutability.mutable => true
  | VarMutability.transient => false
  | VarMutability.constant => false
  | VarMutability.immutable => false

def StateVarDecl.isTransient (decl : StateVarDecl) : Bool :=
  match decl.mutability with
  | VarMutability.transient => true
  | _ => false

def StateVarDecl.constantEntry? (decl : StateVarDecl) :
    Option (Name × Expr) :=
  match decl.mutability, decl.init with
  | VarMutability.constant, some expr => some (decl.name, expr)
  | _, _ => none

def StateVarDecl.hasRequiredConstantInit (decl : StateVarDecl) : Bool :=
  match decl.mutability, decl.init with
  | VarMutability.constant, some _ => true
  | VarMutability.constant, none => false
  | _, _ => true

def StateVars.constantEnv (decls : List StateVarDecl) : ConstantEnv :=
  decls.filterMap StateVarDecl.constantEntry?

def StateVars.constantsHaveInits : List StateVarDecl -> Bool
  | [] => true
  | decl :: rest =>
      StateVarDecl.hasRequiredConstantInit decl &&
        StateVars.constantsHaveInits rest

def StateVars.allConstants : List StateVarDecl -> Bool
  | [] => true
  | decl :: rest =>
      StateVarDecl.isConstant decl && StateVars.allConstants rest

def ContractDecl.directStorageStateVars (decl : ContractDecl) :
    List StateVarDecl :=
  (ContractDecl.directStateVars decl).filter StateVarDecl.isStorageBacked

def ContractDecl.directTransientStateVars (decl : ContractDecl) :
    List StateVarDecl :=
  (ContractDecl.directStateVars decl).filter StateVarDecl.isTransient

def ContractDecl.directImmutableStateVars (decl : ContractDecl) :
    List StateVarDecl :=
  (ContractDecl.directStateVars decl).filter StateVarDecl.isImmutable

def ContractDecl.storageNames (decl : ContractDecl) : List Name :=
  (ContractDecl.directStorageStateVars decl).map StateVarDecl.name ++
    (ContractDecl.directTransientStateVars decl).map StateVarDecl.name

def ContractDecl.directModifiers (decl : ContractDecl) : List SourceModifierDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.modifierDecl modifier => some modifier
    | _ => none)

def ContractDecl.modifiers (decl : ContractDecl) : List SourceModifierDecl :=
  ContractDecl.directModifiers decl

def ContractDecl.directFunctions (decl : ContractDecl) : List FunctionDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.function fn => some fn
    | _ => none)

def ContractDecl.directConstructors (decl : ContractDecl) : List FunctionDecl :=
  (ContractDecl.directFunctions decl).filter FunctionDecl.isConstructor

def ContractDecl.constructorPayable? (decl : ContractDecl) : Option Bool :=
  match ContractDecl.directConstructors decl with
  | [] => some false
  | [ctor] => some (FunctionDecl.isPayable ctor)
  | _ => none

def ContractDecl.directConstructor? (decl : ContractDecl) :
    Option (Option FunctionDecl) :=
  match ContractDecl.directConstructors decl with
  | [] => some none
  | [ctor] => some (some ctor)
  | _ => none

def ContractDecl.directOrdinaryFunctions (decl : ContractDecl) : List FunctionDecl :=
  (ContractDecl.directFunctions decl).filter
    (fun fn => !FunctionDecl.isConstructor fn)

def ContractDecl.isInterface (decl : ContractDecl) : Bool :=
  match decl.kind with
  | ContractKind.interface => true
  | _ => false

def ContractDecl.interfaceId? (decl : ContractDecl) : Option Word := do
  if ContractDecl.isInterface decl then
    some ()
  else
    none
  FunctionDecls.interfaceId? (ContractDecl.directOrdinaryFunctions decl)

def ContractDecl.interfaceIdEntry? (decl : ContractDecl) :
    Option (Option (Name × Word)) :=
  if ContractDecl.isInterface decl then
    do
    let interfaceId ← ContractDecl.interfaceId? decl
    some (some (decl.name, interfaceId))
  else
    some none

def ContractDecls.interfaceIdEnv (decls : List ContractDecl) :
    Option InterfaceIdEnv :=
  filterMapOption ContractDecl.interfaceIdEntry? decls

def ContractItem.resolveInterfaceIds (env : InterfaceIdEnv) :
    ContractItem -> ContractItem
  | ContractItem.stateVar decl =>
      ContractItem.stateVar (StateVarDecl.resolveInterfaceIds env decl)
  | ContractItem.function decl =>
      ContractItem.function (FunctionDecl.resolveInterfaceIds env decl)
  | ContractItem.modifierDecl decl =>
      ContractItem.modifierDecl (ModifierDecl.resolveInterfaceIds env decl)
  | item => item

def BaseSpecifier.resolveInterfaceIds (env : InterfaceIdEnv)
    (spec : BaseSpecifier) : BaseSpecifier :=
  { spec with args := spec.args.map (Expr.resolveInterfaceIds env) }

def ContractDecl.resolveInterfaceIds (env : InterfaceIdEnv)
    (decl : ContractDecl) : ContractDecl :=
  { decl with
    bases := decl.bases.map (BaseSpecifier.resolveInterfaceIds env)
    items := decl.items.map (ContractItem.resolveInterfaceIds env) }

def ContractDecl.contextualOrdinaryFunctions (constants : ConstantEnv)
    (baseNames : List Name) (decl : ContractDecl) : List FunctionDecl :=
  (ContractDecl.directOrdinaryFunctions decl).map
    (fun fn =>
      FunctionDecl.rewriteDispatchCalls decl.name baseNames
        (FunctionDecl.inlineConstants constants fn))

def ContractDecl.contextualBaseHelpers (constants : ConstantEnv)
    (baseNames : List Name) (decl : ContractDecl) : List FunctionDecl :=
  (ContractDecl.contextualOrdinaryFunctions constants baseNames decl).filterMap
    (FunctionDecl.asBaseHelper? decl.name)

def ContractDecl.directUsingDecls (decl : ContractDecl) : List UsingDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.usingDecl usingDecl => some usingDecl
    | _ => none)

def FunctionDecl.asLibraryHelper? (libraryName : Name)
    (decl : FunctionDecl) : Option FunctionDecl :=
  if !FunctionDecl.isInlineLibraryFunction decl then
    none
  else
    match decl.name with
    | some functionName =>
        some { decl with
          name := some (libraryHelperName libraryName functionName) }
    | none => none

def ContractDecl.libraryHelperFunctions
    (contracts : List ContractDecl) : List FunctionDecl :=
  concatMapList
    (fun decl =>
      if ContractDecl.isLibrary decl then
        (ContractDecl.directOrdinaryFunctions decl).filterMap
          (FunctionDecl.asLibraryHelper? decl.name)
      else
        [])
    contracts

def ContractDecls.afterName? : List ContractDecl -> Name ->
    Option (List ContractDecl)
  | [], _ => none
  | decl :: rest, name =>
      if decl.name == name then
        some rest
      else
        ContractDecls.afterName? rest name

def ContractDecls.contextualOrdinaryFunctions (constants : ConstantEnv)
    (baseNames : List Name) (decls : List ContractDecl) :
    List FunctionDecl :=
  concatMapList
    (ContractDecl.contextualOrdinaryFunctions constants baseNames)
    decls

def ContractDecls.contextualBaseHelpers (constants : ConstantEnv)
    (baseNames : List Name) (decls : List ContractDecl) :
    List FunctionDecl :=
  concatMapList
    (ContractDecl.contextualBaseHelpers constants baseNames)
    decls

def ContractDecls.contextualSuperHelpersFor? (constants : ConstantEnv)
    (baseNames : List Name) (dispatchOrder : List ContractDecl)
    (decl : ContractDecl) : Option (List FunctionDecl) := do
  let supers ← ContractDecls.afterName? dispatchOrder decl.name
  some
    ((ContractDecls.contextualOrdinaryFunctions constants baseNames supers)
      |>.filterMap (FunctionDecl.asSuperHelper? decl.name))

def ContractDecls.contextualSuperHelpers? (constants : ConstantEnv)
    (baseNames : List Name) (dispatchOrder : List ContractDecl) :
    Option (List FunctionDecl) := do
  let groups ←
    mapOption
      (ContractDecls.contextualSuperHelpersFor? constants baseNames dispatchOrder)
      dispatchOrder
  some (concatLists groups)

def ContractDecl.directEvents (decl : ContractDecl) : List EventDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.eventDecl event => some event
    | _ => none)

def ContractDecl.directErrors (decl : ContractDecl) : List ErrorDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.errorDecl err => some err
    | _ => none)

def ContractDecl.directStructs (decl : ContractDecl) : List StructDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.structDecl structDecl => some structDecl
    | _ => none)

def ContractDecl.directEnums (decl : ContractDecl) : List EnumDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.enumDecl enumDecl => some enumDecl
    | _ => none)

def ContractDecl.directUserValueTypes
    (decl : ContractDecl) : List UserValueTypeDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.userValueTypeDecl userTy => some userTy
    | _ => none)

def UserTypeEnv.extendDecls (env : UserTypeEnv) :
    List UserValueTypeDecl -> UserTypeEnv
  | [] => env
  | decl :: rest =>
      UserTypeEnv.extendDecls
        (UserTypeEnv.extendDecl env decl) rest

def ContractDecl.userTypeEnvFromContracts (contracts : List ContractDecl) :
    UserTypeEnv :=
  contracts.foldl
    (fun env decl =>
      UserTypeEnv.extendDecls env
        (ContractDecl.directUserValueTypes decl))
    []

def EnumEnv.extendDecls (env : EnumEnv) :
    List EnumDecl -> EnumEnv
  | [] => env
  | decl :: rest =>
      EnumEnv.extendDecls (EnumEnv.extendDecl env decl) rest

def ContractDecl.enumEnvFromContracts (contracts : List ContractDecl) :
    EnumEnv :=
  contracts.foldl
    (fun env decl =>
      EnumEnv.extendDecls env (ContractDecl.directEnums decl))
    []

def StructEnv.extendDecls (env : StructEnv) :
    List StructDecl -> StructEnv
  | [] => env
  | decl :: rest =>
      StructEnv.extendDecls (StructEnv.extendDecl env decl) rest

def ContractDecl.structEnvFromContracts (contracts : List ContractDecl) :
    StructEnv :=
  contracts.foldl
    (fun env decl =>
      StructEnv.extendDecls env (ContractDecl.directStructs decl))
    []

def ContractDecl.findByName? (contracts : List ContractDecl)
    (name : Name) : Option ContractDecl :=
  contracts.find? (fun decl => decl.name == name)

def ModifierInvocation.targetsContract? (contracts : List ContractDecl)
    (invocation : ModifierInvocation) : Bool :=
  match pathLast? invocation.target with
  | some name =>
      match ContractDecl.findByName? contracts name with
      | some _ => true
      | none => false
  | none => false

def ModifierInvocations.dropBaseConstructorInvocations
    (contracts : List ContractDecl) :
    List ModifierInvocation -> List ModifierInvocation
  | [] => []
  | invocation :: rest =>
      let tail :=
        ModifierInvocations.dropBaseConstructorInvocations contracts rest
      if ModifierInvocation.targetsContract? contracts invocation then
        tail
      else
        invocation :: tail

def ModifierInvocations.baseConstructorArgsFor?
    (baseDecl : ContractDecl) (baseCtor? : Option FunctionDecl) :
    List ModifierInvocation -> Option (Option (List Expr))
  | [] => some none
  | invocation :: rest => do
      let tail ←
        ModifierInvocations.baseConstructorArgsFor?
          baseDecl baseCtor? rest
      if pathMatchesName invocation.target baseDecl.name then
        match tail with
        | some _ => none
        | none =>
            let params :=
              match baseCtor? with
              | some ctor => ctor.params
              | none => []
            let args ← Args.toExprsForParams? params invocation.args
            some (some args)
      else
        some tail

def ContractDecl.baseConstructorModifierArgs? (targetDecl baseDecl : ContractDecl) :
    Option (Option (List Expr)) := do
  let targetCtor? ← ContractDecl.directConstructor? targetDecl
  match targetCtor? with
  | none => some none
  | some targetCtor =>
      let baseCtor? ← ContractDecl.directConstructor? baseDecl
      ModifierInvocations.baseConstructorArgsFor?
        baseDecl baseCtor? targetCtor.modifiers

def ContractDecl.baseConstructorArgsForDeployment?
    (targetDecl immediateDerived baseDecl : ContractDecl) :
    Option (List Expr) := do
  let spec ← ContractDecl.baseSpecifierFor? immediateDerived baseDecl
  let modifierArgs? ←
    ContractDecl.baseConstructorModifierArgs? targetDecl baseDecl
  match modifierArgs? with
  | some args =>
      match spec.args with
      | [] => some args
      | _ :: _ => none
  | none => some spec.args

def ContractDecl.baseDecls? (contracts : List ContractDecl)
    (decl : ContractDecl) : Option (List ContractDecl) :=
  mapOption
    (fun base => do
      let name ← pathLast? base.base
      ContractDecl.findByName? contracts name)
    decl.bases

def ContractDecl.storageOrderWithFuel?
    (fuel : Nat) (contracts : List ContractDecl) (decl : ContractDecl) :
    Option (List ContractDecl) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
      let bases ← ContractDecl.baseDecls? contracts decl
      let baseOrders ←
        mapOption
          (fun base => ContractDecl.storageOrderWithFuel? fuel contracts base)
          bases
      some (appendUniqueContracts (concatLists baseOrders) [decl])

def ContractDecl.storageOrder? (contracts : List ContractDecl)
    (decl : ContractDecl) : Option (List ContractDecl) :=
  ContractDecl.storageOrderWithFuel? (contracts.length + 1) contracts decl

def ContractDecls.nonempty : List (List ContractDecl) ->
    List (List ContractDecl)
  | [] => []
  | [] :: rest => ContractDecls.nonempty rest
  | seq@(_ :: _) :: rest => seq :: ContractDecls.nonempty rest

def ContractDecls.nameInTail (name : Name) : List ContractDecl -> Bool
  | [] => false
  | _ :: rest => nameIn name (rest.map ContractDecl.name)

def ContractDecls.nameInAnyTail (name : Name) :
    List (List ContractDecl) -> Bool
  | [] => false
  | seq :: rest =>
      ContractDecls.nameInTail name seq ||
        ContractDecls.nameInAnyTail name rest

def ContractDecls.findMergeCandidateLoop?
    (allSeqs : List (List ContractDecl)) :
    List (List ContractDecl) -> Option ContractDecl
  | [] => none
  | [] :: rest => ContractDecls.findMergeCandidateLoop? allSeqs rest
  | (candidate :: _) :: rest =>
      if ContractDecls.nameInAnyTail candidate.name allSeqs then
        ContractDecls.findMergeCandidateLoop? allSeqs rest
      else
        some candidate

def ContractDecls.findMergeCandidate? (seqs : List (List ContractDecl)) :
    Option ContractDecl :=
  ContractDecls.findMergeCandidateLoop? seqs seqs

def ContractDecls.removeName (name : Name) : List ContractDecl ->
    List ContractDecl
  | [] => []
  | decl :: rest =>
      if decl.name == name then
        ContractDecls.removeName name rest
      else
        decl :: ContractDecls.removeName name rest

def ContractDecls.removeNameFromSeqs (name : Name) :
    List (List ContractDecl) -> List (List ContractDecl)
  | [] => []
  | seq :: rest =>
      ContractDecls.removeName name seq ::
        ContractDecls.removeNameFromSeqs name rest

def ContractDecls.mergeLinearizationsWithFuel? :
    Nat -> List (List ContractDecl) -> Option (List ContractDecl)
  | 0, _ => none
  | fuel + 1, seqs =>
      let seqs := ContractDecls.nonempty seqs
      match seqs with
      | [] => some []
      | _ => do
          let candidate ← ContractDecls.findMergeCandidate? seqs
          let rest ←
            ContractDecls.mergeLinearizationsWithFuel? fuel
              (ContractDecls.removeNameFromSeqs candidate.name seqs)
          some (candidate :: rest)

def ContractDecl.dispatchOrderWithFuel?
    (fuel : Nat) (contracts : List ContractDecl) (decl : ContractDecl) :
    Option (List ContractDecl) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
      let bases ← ContractDecl.baseDecls? contracts decl
      let reversedBases := bases.reverse
      let baseOrders ←
        mapOption
          (fun base => ContractDecl.dispatchOrderWithFuel? fuel contracts base)
          reversedBases
      let merged ←
        ContractDecls.mergeLinearizationsWithFuel? (contracts.length + 1)
          (baseOrders ++ [reversedBases])
      some (decl :: merged)

def ContractDecl.dispatchOrder? (contracts : List ContractDecl)
    (decl : ContractDecl) : Option (List ContractDecl) :=
  ContractDecl.dispatchOrderWithFuel? (contracts.length + 1) contracts decl

def ContractDecl.storageFieldsFrom (transient : Bool) (slot : Nat) :
    List StateVarDecl -> List CoreStorageField
  | [] => []
  | stateVar :: rest =>
      { name := stateVar.name
        slot := slot
        ty? := Ty.toCoreStorageWord? stateVar.ty
        layout? := Ty.toCoreStorageLayout? stateVar.ty
        transient := transient } ::
        ContractDecl.storageFieldsFrom transient (slot + 1) rest

def ContractDecl.toCoreStorageFieldsFrom (transient : Bool)
    (stateVars : List StateVarDecl) : List CoreStorageField :=
  ContractDecl.storageFieldsFrom transient 0 stateVars

def ContractDecl.toCoreStorageFields (decl : ContractDecl) :
    List CoreStorageField :=
  ContractDecl.toCoreStorageFieldsFrom false
    (ContractDecl.directStorageStateVars decl) ++
    ContractDecl.toCoreStorageFieldsFrom true
      (ContractDecl.directTransientStateVars decl)

def StateVarDecl.toCoreImmutableField?
    (decl : StateVarDecl) : Option (Option CoreImmutableField) :=
  match decl.mutability with
  | VarMutability.immutable => do
      let ty ← Ty.toCoreStorageWord? decl.ty
      some (some { name := decl.name, ty := ty })
  | _ => some none

def ContractDecl.toCoreImmutableFieldsFrom
    (stateVars : List StateVarDecl) : Option (List CoreImmutableField) :=
  filterMapOption StateVarDecl.toCoreImmutableField? stateVars

def ContractDecl.toCoreImmutableFields
    (decl : ContractDecl) : Option (List CoreImmutableField) :=
  ContractDecl.toCoreImmutableFieldsFrom
    (ContractDecl.directStateVars decl)

def EventParam.toCoreField? (param : EventParam) :
    Option SolidCore.Solidity.Source.EventField := do
  let ty ← Ty.toCore? param.ty
  some { ty := ty, indexed := param.indexed }

def EventDecl.abiSignature? (decl : EventDecl) : Option String := do
  let paramTypes ←
    mapOption (fun param => Ty.abiCanonical? param.ty) decl.params
  some (decl.name ++ "(" ++ joinStringsWith "," paramTypes ++ ")")

def EventDecl.toCore (decl : EventDecl) : Option CoreEventDecl := do
  let fields ← mapOption EventParam.toCoreField? decl.params
  let signature ← EventDecl.abiSignature? decl
  some
    { name := decl.name
      indexedCount := decl.params.filter (fun param => param.indexed) |>.length
      topic? :=
        if decl.anonymous then
          none
        else
          some
            (SolidCore.Solidity.Source.Keccak.digestWord signature)
      fields := fields }

def ErrorDecl.toCore (decl : ErrorDecl) : Option CoreErrorDecl := do
  let fields ← Parameters.toCoreBindings? "_err" decl.params
  let types ← Parameters.abiCanonicalTypes? decl.params
  let signature := decl.name ++ "(" ++ joinStringsWith "," types ++ ")"
  some
    { name := decl.name
      selector :=
        SolidCore.Solidity.Source.ABI.selectorFromSignature
          signature
      fields := fields.map (fun field => field.ty) }

def StateVarDecl.toCoreMappingGetterIfPublic?
    (decl : StateVarDecl) : Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.ty with
  | some Visibility.public_, Ty.mapping keyTy valueTy => do
      let keyCoreTy ← Ty.toCoreMappingKey? keyTy
      let valueCoreTy ← Ty.toCoreStorageWord? valueTy
      let keyCanonical ← Ty.abiCanonical? keyTy
      let signature := decl.name ++ "(" ++ keyCanonical ++ ")"
      let keyName := "_key0"
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  signature)
            params := [{ name := keyName, ty := keyCoreTy }]
            returns := [{ name := "_value", ty := valueCoreTy }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues
                [SolidCore.Solidity.Source.Expr.storageIndex
                  decl.name
                  (SolidCore.Solidity.Source.Expr.var keyName)] })
  | some Visibility.public_, _ => some none
  | _, _ => some none

def StateVarDecl.toCoreArrayGetterIfPublic?
    (decl : StateVarDecl) : Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.ty with
  | some Visibility.public_, Ty.array elementTy _ => do
      let elementCoreTy ← Ty.toCoreStorageWord? elementTy
      let indexName := "_index0"
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  (decl.name ++ "(uint256)"))
            params :=
              [{ name := indexName
                 ty := SolidCore.Solidity.Source.Ty.uint256 }]
            returns := [{ name := "_value", ty := elementCoreTy }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues
                [SolidCore.Solidity.Source.Expr.storageIndex
                  decl.name
                  (SolidCore.Solidity.Source.Expr.var indexName)] })
  | some Visibility.public_, _ => some none
  | _, _ => some none

def StateVarDecl.toCoreByteStringGetterIfPublic?
    (decl : StateVarDecl) : Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.ty with
  | some Visibility.public_, Ty.bytes =>
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  (decl.name ++ "()"))
            params := []
            returns :=
              [{ name := "_value"
                 ty := SolidCore.Solidity.Source.Ty.bytesCalldata }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues
                [SolidCore.Solidity.Source.Expr.storageBytes decl.name] })
  | some Visibility.public_, Ty.string =>
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  (decl.name ++ "()"))
            params := []
            returns :=
              [{ name := "_value"
                 ty := SolidCore.Solidity.Source.Ty.bytesCalldata }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues
                [SolidCore.Solidity.Source.Expr.storageBytes decl.name] })
  | some Visibility.public_, _ => some none
  | _, _ => some none

def StateVarDecl.toCoreStructGetterIfPublic?
    (decl : StateVarDecl) : Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.ty with
  | some Visibility.public_, Ty.tuple _ => do
      let ty ← Ty.toCore? decl.ty
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  (decl.name ++ "()"))
            params := []
            returns := [{ name := "_value", ty := ty }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues
                [SolidCore.Solidity.Source.Expr.storage decl.name] })
  | some Visibility.public_, _ => some none
  | _, _ => some none

def StateVarDecl.toCoreConstantGetterIfPublic?
    (storageNames : List Name) (constants : ConstantEnv)
    (decl : StateVarDecl) : Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.mutability, decl.init with
  | some Visibility.public_, VarMutability.constant, some init => do
      let ty ← Ty.toCore? decl.ty
      let initCore ←
        Expr.toCore? storageNames (Expr.inlineConstants constants init)
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  (decl.name ++ "()"))
            params := []
            returns := [{ name := "_value", ty := ty }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues [initCore] })
  | some Visibility.public_, VarMutability.constant, none => none
  | some Visibility.public_, VarMutability.immutable, _ => none
  | _, _, _ => some none

def StateVarDecl.toCoreImmutableGetterIfPublic?
    (decl : StateVarDecl) : Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.mutability with
  | some Visibility.public_, VarMutability.immutable => do
      let ty ← Ty.toCoreStorageWord? decl.ty
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  (decl.name ++ "()"))
            params := []
            returns := [{ name := "_value", ty := ty }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues
                [SolidCore.Solidity.Source.Expr.immutable decl.name] })
  | some Visibility.public_, _ => some none
  | _, _ => some none

def StateVarDecl.toCoreGetterIfPublic? (storageNames : List Name)
    (constants : ConstantEnv) (decl : StateVarDecl) :
    Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.mutability with
  | some Visibility.public_, VarMutability.constant =>
      StateVarDecl.toCoreConstantGetterIfPublic?
        storageNames constants decl
  | some Visibility.public_, VarMutability.immutable =>
      StateVarDecl.toCoreImmutableGetterIfPublic? decl
  | some Visibility.public_, VarMutability.mutable
  | some Visibility.public_, VarMutability.transient => do
      match StateVarDecl.toCoreMappingGetterIfPublic? decl with
      | some (some getter) => some (some getter)
      | some none => do
          match StateVarDecl.toCoreArrayGetterIfPublic? decl with
          | some (some getter) => some (some getter)
          | some none => do
              match StateVarDecl.toCoreStructGetterIfPublic? decl with
              | some (some getter) => some (some getter)
              | some none => do
                  match StateVarDecl.toCoreByteStringGetterIfPublic? decl with
                  | some (some getter) => some (some getter)
                  | some none => do
                      let ty ← Ty.toCoreStorageWord? decl.ty
                      some
                        (some
                          { name := decl.name
                            selector? :=
                              some
                                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                                  (decl.name ++ "()"))
                            params := []
                            returns := [{ name := "_value", ty := ty }]
                            body :=
                              SolidCore.Solidity.Source.Stmt.returnValues
                                [SolidCore.Solidity.Source.Expr.storage decl.name] })
                  | none => none
              | none => none
          | none => none
      | none => none
  | _, _ => some none

def StateVarDecl.toCoreInit? (storageNames : List Name)
    (constants : ConstantEnv)
    (decl : StateVarDecl) : Option CoreStmt :=
  match decl.mutability, decl.init with
  | VarMutability.mutable, some expr => do
      let expr := Expr.inlineConstants constants expr
      let initCore ← Expr.toCore? storageNames expr
      some (SolidCore.Solidity.Source.Stmt.assign
        (SolidCore.Solidity.Source.LValue.storage decl.name)
        initCore)
  | VarMutability.transient, some expr => do
      let expr := Expr.inlineConstants constants expr
      let initCore ← Expr.toCore? storageNames expr
      some (SolidCore.Solidity.Source.Stmt.assign
        (SolidCore.Solidity.Source.LValue.storage decl.name)
        initCore)
  | VarMutability.immutable, some expr => do
      let expr := Expr.inlineConstants constants expr
      let initCore ← Expr.toCore? storageNames expr
      some (SolidCore.Solidity.Source.Stmt.assign
        (SolidCore.Solidity.Source.LValue.immutable decl.name)
        initCore)
  | _, _ => some SolidCore.Solidity.Source.Stmt.skip

def ContractDecl.directCoreFunctions? (storageNames : List Name)
    (constants : ConstantEnv)
    (extraEnv : TypeEnv) (contracts : List ContractDecl)
    (dispatchOrder : List ContractDecl)
    (sourceUsingDecls : List UsingDecl)
    (modifiers : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl) (decl : ContractDecl) :
    Option (List CoreFunctionDef) := do
  let getters ←
    filterMapOption (StateVarDecl.toCoreGetterIfPublic? storageNames constants)
      (ContractDecl.directStateVars decl)
  let usingDecls := ContractDecl.directUsingDecls decl ++ sourceUsingDecls
  let functions ←
    mapOption
      (fun fn => do
        let supers ← ContractDecls.afterName? dispatchOrder decl.name
        FunctionDecl.toCore?
          storageNames constants extraEnv contracts usingDecls modifiers functions
          freeFunctions fn (concatMapList ContractDecl.directOrdinaryFunctions supers)
          (some decl.name) (dispatchOrder.map ContractDecl.name))
      ((ContractDecl.directOrdinaryFunctions decl).filter
        FunctionDecl.isCoreEntrypoint)
  some (getters ++ functions)

def ContractDecl.constructorBodyForDeployment?
    (allContracts : List ContractDecl)
    (sourceUsingDecls : List UsingDecl)
    (storageNames : List Name) (constants : ConstantEnv)
    (stateEnv : TypeEnv)
    (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (targetName : Name) (baseArgs : List Expr) (decl : ContractDecl) :
    Option (List CoreBindingDecl × List CoreStmt) := do
  let initStmts ←
    mapOption
      (StateVarDecl.toCoreInit? storageNames constants)
      (ContractDecl.directStateVars decl)
  let baseArgs := baseArgs.map (Expr.inlineConstants constants)
  match ContractDecl.directConstructors decl with
  | [] => some ([], initStmts)
  | [ctor] => do
      let ctor := FunctionDecl.inlineConstants constants ctor
      let (params, baseArgStmts) ←
        if decl.name == targetName then
          let params ← Parameters.toCoreBindings? "_arg" ctor.params
          some (params, [])
        else
          let argDecls ←
            Parameters.toVarDeclsWithArgs? "_arg" ctor.params baseArgs
          some ([], argDecls)
      let baseArgCore ← Stmt.listToCore? storageNames baseArgStmts
      let body :=
        match ctor.body with
        | some stmt => stmt
        | none => Stmt.empty
      let body := Stmt.inlineConstants constants body
      let usingDecls := ContractDecl.directUsingDecls decl ++ sourceUsingDecls
      let env := FunctionDecl.typeEnv stateEnv ctor
      let body :=
        if usingDecls.isEmpty && !ContractDecls.hasLibrary allContracts then
          body
        else
          Stmt.expandUsing allContracts usingDecls env body
      let modifiers :=
        if usingDecls.isEmpty && !ContractDecls.hasLibrary allContracts then
          modifiers
        else
          modifiers.map (ModifierDecl.expandUsing allContracts usingDecls env)
      let body := Stmt.annotateAbi env body
      let storageRefEnv := Parameters.extendStorageRefEnv "_arg" [] ctor.params
      let ctorModifiers :=
        ModifierInvocations.dropBaseConstructorInvocations
          allContracts ctor.modifiers
      let ctorModifiers :=
        if usingDecls.isEmpty && !ContractDecls.hasLibrary allContracts then
          ctorModifiers
        else
          ctorModifiers.map
            (ModifierInvocation.expandUsing allContracts usingDecls env)
      let bodyCore ←
        functionExpandModifiersToCoreWithInternalCallsFull?
          defaultInternalCallInlineFuel storageRefEnv env storageNames []
          modifiers functions freeFunctions [] ctorModifiers body
      if decl.name == targetName then
        some (params, initStmts ++ [bodyCore])
      else
        some
          (params,
            initStmts ++
              [SolidCore.Solidity.Source.Stmt.block
                (baseArgCore ++ [bodyCore])])
  | _ => none

def ContractDecl.toCoreFromOrders? (allContracts : List ContractDecl)
    (sourceUsingDecls : List UsingDecl)
    (sourceFunctions : List FunctionDecl) (sourceErrors : List ErrorDecl)
    (sourceConstants : List StateVarDecl)
    (storageOrder dispatchOrder : List ContractDecl) :
    Option CoreContract := do
  let allContracts :=
    appendUniqueContracts allContracts
      (appendUniqueContracts storageOrder dispatchOrder)
  let userEnv :=
    ContractDecl.userTypeEnvFromContracts allContracts
  let enumEnv :=
    ContractDecl.enumEnvFromContracts allContracts
  let allContracts :=
    (allContracts.map (ContractDecl.resolveUserTypes userEnv)).map
      (ContractDecl.resolveEnums enumEnv)
  let sourceUsingDecls :=
    (sourceUsingDecls.map (UsingDecl.resolveUserTypes userEnv)).map
      (UsingDecl.resolveEnums enumEnv)
  let sourceConstants :=
    (sourceConstants.map (StateVarDecl.resolveUserTypes userEnv)).map
      (StateVarDecl.resolveEnums enumEnv)
  let storageOrder :=
    (storageOrder.map (ContractDecl.resolveUserTypes userEnv)).map
      (ContractDecl.resolveEnums enumEnv)
  let dispatchOrder :=
    (dispatchOrder.map (ContractDecl.resolveUserTypes userEnv)).map
      (ContractDecl.resolveEnums enumEnv)
  let structEnv := ContractDecl.structEnvFromContracts allContracts
  let allContracts := allContracts.map (ContractDecl.resolveStructs structEnv)
  let sourceUsingDecls := sourceUsingDecls.map (UsingDecl.resolveStructs structEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveStructs structEnv)
  let storageOrder := storageOrder.map (ContractDecl.resolveStructs structEnv)
  let dispatchOrder := dispatchOrder.map (ContractDecl.resolveStructs structEnv)
  let interfaceIdEnv ← ContractDecls.interfaceIdEnv allContracts
  let allContracts := allContracts.map (ContractDecl.resolveInterfaceIds interfaceIdEnv)
  let sourceFunctions := sourceFunctions.map (FunctionDecl.resolveInterfaceIds interfaceIdEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveInterfaceIds interfaceIdEnv)
  let storageOrder :=
    storageOrder.map (ContractDecl.resolveInterfaceIds interfaceIdEnv)
  let dispatchOrder :=
    dispatchOrder.map (ContractDecl.resolveInterfaceIds interfaceIdEnv)
  let stateVars := concatMapList ContractDecl.directStateVars storageOrder
  if !namesUnique (sourceConstants.map StateVarDecl.name) then
    none
  else
    some ()
  if !StateVars.allConstants sourceConstants then
    none
  else
    some ()
  if !StateVars.constantsHaveInits sourceConstants then
    none
  else
    some ()
  if !namesUnique (stateVars.map StateVarDecl.name) then
    none
  else
    some ()
  if !StateVars.constantsHaveInits stateVars then
    none
  else
    some ()
  let selectorEnv :=
    FunctionDecls.selectorEntries
      (sourceFunctions ++ concatMapList ContractDecl.directOrdinaryFunctions dispatchOrder) ++
    ErrorDecls.selectorEntries
      (sourceErrors ++ concatMapList ContractDecl.directErrors dispatchOrder) ++
    StateVarDecls.selectorEntries stateVars
  let functionAddressEnv :=
    FunctionDecls.selectorEntries
      (sourceFunctions ++ concatMapList ContractDecl.directOrdinaryFunctions dispatchOrder) ++
    StateVarDecls.selectorEntries stateVars
  let allContracts :=
    allContracts.map (ContractDecl.resolveFunctionAddresses functionAddressEnv)
  let sourceFunctions :=
    sourceFunctions.map (FunctionDecl.resolveFunctionAddresses functionAddressEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveFunctionAddresses functionAddressEnv)
  let storageOrder :=
    storageOrder.map (ContractDecl.resolveFunctionAddresses functionAddressEnv)
  let dispatchOrder :=
    dispatchOrder.map (ContractDecl.resolveFunctionAddresses functionAddressEnv)
  let allContracts := allContracts.map (ContractDecl.resolveSelectors selectorEnv)
  let sourceFunctions := sourceFunctions.map (FunctionDecl.resolveSelectors selectorEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveSelectors selectorEnv)
  let storageOrder := storageOrder.map (ContractDecl.resolveSelectors selectorEnv)
  let dispatchOrder := dispatchOrder.map (ContractDecl.resolveSelectors selectorEnv)
  let stateVars := concatMapList ContractDecl.directStateVars storageOrder
  let sourceConstantEnv := StateVars.constantEnv sourceConstants
  let constants := StateVars.constantEnv stateVars ++ sourceConstantEnv
  let storageStateVars := stateVars.filter StateVarDecl.isStorageBacked
  let transientStateVars := stateVars.filter StateVarDecl.isTransient
  let immutableStateVars := stateVars.filter StateVarDecl.isImmutable
  let storageNames :=
    stateNamesFrom (storageStateVars ++ transientStateVars) immutableStateVars
  let stateEnv := StateVars.extendTypeEnv [] stateVars
  let modifiers :=
    (concatMapList ContractDecl.directModifiers dispatchOrder).map
      (ModifierDecl.inlineConstants constants)
  let baseNames := dispatchOrder.map ContractDecl.name
  let ordinaryFunctions :=
    ContractDecls.contextualOrdinaryFunctions constants baseNames dispatchOrder
  let libraryHelpers :=
    (ContractDecl.libraryHelperFunctions allContracts).map
      (FunctionDecl.inlineConstants constants)
  let baseHelpers :=
    ContractDecls.contextualBaseHelpers constants baseNames dispatchOrder
  let superHelpers ←
    ContractDecls.contextualSuperHelpers? constants baseNames dispatchOrder
  let sourceFunctions :=
    sourceFunctions.map (FunctionDecl.inlineConstants sourceConstantEnv)
  let availableFunctions :=
    ordinaryFunctions ++ superHelpers ++ baseHelpers ++ libraryHelpers
  let functionGroups ←
    mapOption
      (ContractDecl.directCoreFunctions?
        storageNames constants stateEnv allContracts dispatchOrder sourceUsingDecls
        modifiers availableFunctions sourceFunctions)
      dispatchOrder
  let functions := concatLists functionGroups
  let immutableFields ←
    ContractDecl.toCoreImmutableFieldsFrom stateVars
  let eventDecls ←
    mapOption EventDecl.toCore
      (concatMapList ContractDecl.directEvents dispatchOrder)
  let errorDecls ←
    mapOption
      ErrorDecl.toCore
      (sourceErrors ++ concatMapList ContractDecl.directErrors dispatchOrder)
  some
    { storageFields :=
        ContractDecl.toCoreStorageFieldsFrom false storageStateVars ++
          ContractDecl.toCoreStorageFieldsFrom true transientStateVars
      immutableFields := immutableFields
      eventDecls := eventDecls
      errorDecls := errorDecls
      functions := functions }

def ContractDecl.constructorFunctionFromOrders?
    (allContracts : List ContractDecl)
    (sourceUsingDecls : List UsingDecl)
    (sourceFunctions : List FunctionDecl)
    (sourceConstants : List StateVarDecl)
    (storageOrder dispatchOrder : List ContractDecl)
    (targetName : Name) : Option CoreFunctionDef := do
  let allContracts :=
    appendUniqueContracts allContracts
      (appendUniqueContracts storageOrder dispatchOrder)
  let userEnv :=
    ContractDecl.userTypeEnvFromContracts allContracts
  let enumEnv :=
    ContractDecl.enumEnvFromContracts allContracts
  let allContracts :=
    (allContracts.map (ContractDecl.resolveUserTypes userEnv)).map
      (ContractDecl.resolveEnums enumEnv)
  let storageOrder :=
    (storageOrder.map (ContractDecl.resolveUserTypes userEnv)).map
      (ContractDecl.resolveEnums enumEnv)
  let dispatchOrder :=
    (dispatchOrder.map (ContractDecl.resolveUserTypes userEnv)).map
      (ContractDecl.resolveEnums enumEnv)
  let sourceUsingDecls :=
    (sourceUsingDecls.map (UsingDecl.resolveUserTypes userEnv)).map
      (UsingDecl.resolveEnums enumEnv)
  let sourceFunctions :=
    (sourceFunctions.map (FunctionDecl.resolveUserTypes userEnv)).map
      (FunctionDecl.resolveEnums enumEnv)
  let sourceConstants :=
    (sourceConstants.map (StateVarDecl.resolveUserTypes userEnv)).map
      (StateVarDecl.resolveEnums enumEnv)
  let structEnv :=
    ContractDecl.structEnvFromContracts allContracts
  let allContracts := allContracts.map (ContractDecl.resolveStructs structEnv)
  let sourceUsingDecls := sourceUsingDecls.map (UsingDecl.resolveStructs structEnv)
  let sourceFunctions := sourceFunctions.map (FunctionDecl.resolveStructs structEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveStructs structEnv)
  let storageOrder := storageOrder.map (ContractDecl.resolveStructs structEnv)
  let dispatchOrder := dispatchOrder.map (ContractDecl.resolveStructs structEnv)
  let interfaceIdEnv ← ContractDecls.interfaceIdEnv allContracts
  let allContracts := allContracts.map (ContractDecl.resolveInterfaceIds interfaceIdEnv)
  let sourceFunctions := sourceFunctions.map (FunctionDecl.resolveInterfaceIds interfaceIdEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveInterfaceIds interfaceIdEnv)
  let storageOrder :=
    storageOrder.map (ContractDecl.resolveInterfaceIds interfaceIdEnv)
  let dispatchOrder :=
    dispatchOrder.map (ContractDecl.resolveInterfaceIds interfaceIdEnv)
  let stateVars := concatMapList ContractDecl.directStateVars storageOrder
  if !namesUnique (sourceConstants.map StateVarDecl.name) then
    none
  else
    some ()
  if !StateVars.allConstants sourceConstants then
    none
  else
    some ()
  if !StateVars.constantsHaveInits sourceConstants then
    none
  else
    some ()
  if !namesUnique (stateVars.map StateVarDecl.name) then
    none
  else
    some ()
  if !StateVars.constantsHaveInits stateVars then
    none
  else
    some ()
  let selectorEnv :=
    FunctionDecls.selectorEntries
      (sourceFunctions ++ concatMapList ContractDecl.directOrdinaryFunctions dispatchOrder) ++
    ErrorDecls.selectorEntries
      (concatMapList ContractDecl.directErrors dispatchOrder) ++
    StateVarDecls.selectorEntries stateVars
  let functionAddressEnv :=
    FunctionDecls.selectorEntries
      (sourceFunctions ++ concatMapList ContractDecl.directOrdinaryFunctions dispatchOrder) ++
    StateVarDecls.selectorEntries stateVars
  let allContracts :=
    allContracts.map (ContractDecl.resolveFunctionAddresses functionAddressEnv)
  let sourceFunctions :=
    sourceFunctions.map (FunctionDecl.resolveFunctionAddresses functionAddressEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveFunctionAddresses functionAddressEnv)
  let storageOrder :=
    storageOrder.map (ContractDecl.resolveFunctionAddresses functionAddressEnv)
  let dispatchOrder :=
    dispatchOrder.map (ContractDecl.resolveFunctionAddresses functionAddressEnv)
  let allContracts := allContracts.map (ContractDecl.resolveSelectors selectorEnv)
  let sourceFunctions := sourceFunctions.map (FunctionDecl.resolveSelectors selectorEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveSelectors selectorEnv)
  let storageOrder := storageOrder.map (ContractDecl.resolveSelectors selectorEnv)
  let dispatchOrder := dispatchOrder.map (ContractDecl.resolveSelectors selectorEnv)
  let stateVars := concatMapList ContractDecl.directStateVars storageOrder
  let sourceConstantEnv := StateVars.constantEnv sourceConstants
  let constants := StateVars.constantEnv stateVars ++ sourceConstantEnv
  let storageStateVars := stateVars.filter StateVarDecl.isStorageBacked
  let transientStateVars := stateVars.filter StateVarDecl.isTransient
  let immutableStateVars := stateVars.filter StateVarDecl.isImmutable
  let storageNames :=
    stateNamesFrom (storageStateVars ++ transientStateVars) immutableStateVars
  let stateEnv := StateVars.extendTypeEnv [] stateVars
  let modifiers :=
    (concatMapList ContractDecl.directModifiers dispatchOrder).map
      (ModifierDecl.inlineConstants constants)
  let baseNames := dispatchOrder.map ContractDecl.name
  let ordinaryFunctions :=
    ContractDecls.contextualOrdinaryFunctions constants baseNames dispatchOrder
  let libraryHelpers :=
    (ContractDecl.libraryHelperFunctions allContracts).map
      (FunctionDecl.inlineConstants constants)
  let baseHelpers :=
    ContractDecls.contextualBaseHelpers constants baseNames dispatchOrder
  let superHelpers ←
    ContractDecls.contextualSuperHelpers? constants baseNames dispatchOrder
  let sourceFunctions :=
    sourceFunctions.map (FunctionDecl.inlineConstants sourceConstantEnv)
  let availableFunctions :=
    ordinaryFunctions ++ superHelpers ++ baseHelpers ++ libraryHelpers
  let targetDecl ← ContractDecl.findByName? dispatchOrder targetName
  let payable ← ContractDecl.constructorPayable? targetDecl
  let pieces ←
    mapOption
      (fun decl => do
        let baseArgs ←
          if decl.name == targetName then
            some []
          else
            let derived ←
              ContractDecl.findImmediateDerivedInOrder?
                storageOrder decl
            ContractDecl.baseConstructorArgsForDeployment?
              targetDecl derived decl
        ContractDecl.constructorBodyForDeployment?
          allContracts sourceUsingDecls storageNames constants stateEnv
          modifiers availableFunctions sourceFunctions targetName baseArgs decl)
      storageOrder
  let params := concatLists (pieces.map Prod.fst)
  let stmts := concatLists (pieces.map Prod.snd)
  some
    { name := "__constructor"
      selector? := none
      payable := payable
      params := params
      returns := []
      body := SolidCore.Solidity.Source.Stmt.block stmts }

def ContractDecl.toCore? (decl : ContractDecl) : Option CoreContract :=
  ContractDecl.toCoreFromOrders? [decl] [] [] [] [] [decl] [decl]

def ContractDecl.toCoreWithBasesAndUsing? (sourceUsingDecls : List UsingDecl)
    (sourceFunctions : List FunctionDecl) (sourceErrors : List ErrorDecl)
    (sourceConstants : List StateVarDecl)
    (contracts : List ContractDecl) (decl : ContractDecl) :
    Option CoreContract := do
  let storageOrder ← ContractDecl.storageOrder? contracts decl
  let dispatchOrder ← ContractDecl.dispatchOrder? contracts decl
  ContractDecl.toCoreFromOrders?
    contracts sourceUsingDecls sourceFunctions sourceErrors sourceConstants
    storageOrder dispatchOrder

def ContractDecl.toCoreWithBases? (contracts : List ContractDecl)
    (decl : ContractDecl) : Option CoreContract := do
  ContractDecl.toCoreWithBasesAndUsing? [] [] [] [] contracts decl

def ContractDecl.constructorFunctionWithBasesAndSource?
    (sourceUsingDecls : List UsingDecl)
    (sourceFunctions : List FunctionDecl)
    (sourceConstants : List StateVarDecl)
    (contracts : List ContractDecl) (decl : ContractDecl) :
    Option CoreFunctionDef := do
  let storageOrder ← ContractDecl.storageOrder? contracts decl
  let dispatchOrder ← ContractDecl.dispatchOrder? contracts decl
  ContractDecl.constructorFunctionFromOrders?
    contracts sourceUsingDecls sourceFunctions sourceConstants
    storageOrder dispatchOrder decl.name

def ContractDecl.constructorFunctionWithBases?
    (contracts : List ContractDecl) (decl : ContractDecl) :
    Option CoreFunctionDef :=
  ContractDecl.constructorFunctionWithBasesAndSource? [] [] [] contracts decl

def ContractDecl.constructWithBasesAndSourceFrom? (fuel : Nat)
    (sourceUsingDecls : List UsingDecl)
    (sourceFunctions : List FunctionDecl)
    (sourceErrors : List ErrorDecl)
    (sourceConstants : List StateVarDecl)
    (contracts : List ContractDecl) (decl : ContractDecl)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult := do
  let contract ←
    ContractDecl.toCoreWithBasesAndUsing?
      sourceUsingDecls sourceFunctions sourceErrors sourceConstants
      contracts decl
  let constructor ←
    ContractDecl.constructorFunctionWithBasesAndSource?
      sourceUsingDecls sourceFunctions sourceConstants contracts decl
  SolidCore.Solidity.Source.FunctionDef.call?
    fuel
    { contract.context with
      sender := sender
      value := value
      construction := true }
    constructor state args

def ContractDecl.constructWithBasesFrom? (fuel : Nat)
    (contracts : List ContractDecl) (decl : ContractDecl)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult :=
  ContractDecl.constructWithBasesAndSourceFrom?
    fuel [] [] [] [] contracts decl state sender value args

def ContractDecl.constructWithBases? (fuel : Nat)
    (contracts : List ContractDecl) (decl : ContractDecl)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult :=
  ContractDecl.constructWithBasesFrom? fuel contracts decl state 0 0 args

def ContractDecl.constructFrom? (fuel : Nat) (decl : ContractDecl)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult :=
  ContractDecl.constructWithBasesFrom? fuel [decl] decl state sender value args

def ContractDecl.construct? (fuel : Nat) (decl : ContractDecl)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult :=
  ContractDecl.constructWithBases? fuel [decl] decl state args

def SourceUnit.freeUserValueTypes (unit : SourceUnit) :
    List UserValueTypeDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.freeUserValueType decl => some decl
    | _ => none)

def SourceUnit.freeEnums (unit : SourceUnit) : List EnumDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.freeEnum decl => some decl
    | _ => none)

def SourceUnit.freeStructs (unit : SourceUnit) : List StructDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.freeStruct decl => some decl
    | _ => none)

def SourceUnit.freeFunctions (unit : SourceUnit) : List FunctionDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.freeFunction decl => some decl
    | _ => none)

def SourceUnit.freeErrors (unit : SourceUnit) : List ErrorDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.freeError decl => some decl
    | _ => none)

def SourceUnit.freeConstants (unit : SourceUnit) : List StateVarDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.freeConstant decl => some decl
    | _ => none)

def SourceUnit.userTypeEnv (unit : SourceUnit) : UserTypeEnv :=
  let freeEnv :=
    UserTypeEnv.extendDecls [] (SourceUnit.freeUserValueTypes unit)
  UserTypeEnv.extendDecls freeEnv
    (concatMapList ContractDecl.directUserValueTypes
      (unit.items.filterMap (fun item =>
        match item with
        | SourceItem.contract decl => some decl
        | _ => none)))

def SourceUnit.resolveUserTypes (unit : SourceUnit) : SourceUnit :=
  let env := SourceUnit.userTypeEnv unit
  { unit with items := unit.items.map (SourceItem.resolveUserTypes env) }

def SourceUnit.enumEnv (unit : SourceUnit) : EnumEnv :=
  let freeEnv := EnumEnv.extendDecls [] (SourceUnit.freeEnums unit)
  EnumEnv.extendDecls freeEnv
    (concatMapList ContractDecl.directEnums
      (unit.items.filterMap (fun item =>
        match item with
        | SourceItem.contract decl => some decl
        | _ => none)))

def SourceUnit.resolveEnums (unit : SourceUnit) : SourceUnit :=
  let env := SourceUnit.enumEnv unit
  { unit with items := unit.items.map (SourceItem.resolveEnums env) }

def SourceUnit.structEnv (unit : SourceUnit) : StructEnv :=
  let freeEnv := StructEnv.extendDecls [] (SourceUnit.freeStructs unit)
  StructEnv.extendDecls freeEnv
    (concatMapList ContractDecl.directStructs
      (unit.items.filterMap (fun item =>
        match item with
        | SourceItem.contract decl => some decl
        | _ => none)))

def SourceUnit.resolveStructs (unit : SourceUnit) : SourceUnit :=
  let env := SourceUnit.structEnv unit
  { unit with items := unit.items.map (SourceItem.resolveStructs env) }

def SourceUnit.resolveSourceTypes (unit : SourceUnit) : SourceUnit :=
  SourceUnit.resolveStructs
    (SourceUnit.resolveEnums (SourceUnit.resolveUserTypes unit))

def SourceUnit.contracts (unit : SourceUnit) : List ContractDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.contract decl => some decl
    | _ => none)

def SourceUnit.usingDecls (unit : SourceUnit) : List UsingDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.usingDecl usingDecl => some usingDecl
    | _ => none)

def SourceUnit.findContract? (unit : SourceUnit)
    (name : Name) : Option ContractDecl :=
  ContractDecl.findByName? (SourceUnit.contracts unit) name

def SourceUnit.toCoreContract? (unit : SourceUnit)
    (name : Name) : Option CoreContract := do
  let unit := SourceUnit.resolveSourceTypes unit
  let decl ← SourceUnit.findContract? unit name
  ContractDecl.toCoreWithBasesAndUsing?
    (SourceUnit.usingDecls unit) (SourceUnit.freeFunctions unit)
    (SourceUnit.freeErrors unit) (SourceUnit.freeConstants unit)
    (SourceUnit.contracts unit) decl

def SourceUnit.constructContract? (fuel : Nat) (unit : SourceUnit)
    (name : Name) (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let unit := SourceUnit.resolveSourceTypes unit
  let decl ← SourceUnit.findContract? unit name
  ContractDecl.constructWithBasesAndSourceFrom? fuel
    (SourceUnit.usingDecls unit) (SourceUnit.freeFunctions unit)
    (SourceUnit.freeErrors unit) (SourceUnit.freeConstants unit)
    (SourceUnit.contracts unit) decl state 0 0 args

def SourceUnit.constructContractFrom? (fuel : Nat) (unit : SourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Option CoreCallResult := do
  let unit := SourceUnit.resolveSourceTypes unit
  let decl ← SourceUnit.findContract? unit name
  ContractDecl.constructWithBasesAndSourceFrom? fuel
    (SourceUnit.usingDecls unit) (SourceUnit.freeFunctions unit)
    (SourceUnit.freeErrors unit) (SourceUnit.freeConstants unit)
    (SourceUnit.contracts unit) decl state sender value args

def SourceUnit.toCoreContracts? (unit : SourceUnit) :
    Option (List CoreContract) :=
  let unit := SourceUnit.resolveSourceTypes unit
  mapOption
    (fun decl =>
      ContractDecl.toCoreWithBasesAndUsing?
        (SourceUnit.usingDecls unit) (SourceUnit.freeFunctions unit)
        (SourceUnit.freeErrors unit) (SourceUnit.freeConstants unit)
        (SourceUnit.contracts unit) decl)
    (SourceUnit.contracts unit)

def Stmt.eval? (fuel : Nat) (storageNames : List Name)
    (context : CoreContext) (runtime : CoreRuntime) (stmt : Stmt) :
    Option CoreResult := do
  let coreStmt ← Stmt.toCore? storageNames stmt
  SolidCore.Solidity.Source.Stmt.eval fuel context runtime coreStmt

def FunctionDecl.call? (fuel : Nat) (storageNames : List Name)
    (modifiers : List SourceModifierDecl)
    (context : CoreContext) (state : CoreState) (decl : FunctionDecl)
    (args : List CoreValue) : Option CoreCallResult := do
  let function ←
    FunctionDecl.toCore?
      (storageNames := storageNames)
      (constants := [])
      (extraEnv := [])
      (contracts := [])
      (usingDecls := [])
      (modifiers := modifiers)
      (functions := [decl])
      (freeFunctions := [])
      (decl := decl)
  SolidCore.Solidity.Source.FunctionDef.call? fuel context function state args

def ContractDecl.call? (fuel : Nat) (decl : ContractDecl)
    (target : SolidCore.Solidity.Source.CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult := do
  let contract ← ContractDecl.toCore? decl
  SolidCore.Solidity.Source.Contract.call? fuel contract target state args

def ContractDecl.callTransaction? (fuel : Nat) (decl : ContractDecl)
    (target : SolidCore.Solidity.Source.CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult := do
  let contract ← ContractDecl.toCore? decl
  SolidCore.Solidity.Source.Contract.callTransaction?
    fuel contract target state args

def SourceUnit.callContract? (fuel : Nat) (unit : SourceUnit)
    (contractName : Name) (target : SolidCore.Solidity.Source.CallTarget)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult := do
  let contract ← SourceUnit.toCoreContract? unit contractName
  SolidCore.Solidity.Source.Contract.call? fuel contract target state args

def SourceUnit.callContractTransaction? (fuel : Nat) (unit : SourceUnit)
    (contractName : Name) (target : SolidCore.Solidity.Source.CallTarget)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult := do
  let contract ← SourceUnit.toCoreContract? unit contractName
  SolidCore.Solidity.Source.Contract.callTransaction?
    fuel contract target state args

def CoreValue.asWord? (value : CoreValue) : Option Word :=
  SolidCore.Solidity.Source.Value.asWord? value

def CoreValue.asLowLevelReturn? (value : CoreValue) :
    Option (Word × List Byte) :=
  match value with
  | SolidCore.Solidity.Source.Value.tuple values =>
      match values with
      | successValue :: outputValue :: [] =>
          match successValue, outputValue with
          | SolidCore.Solidity.Source.Value.word success,
              SolidCore.Solidity.Source.Value.bytes output =>
              some (success, output)
          | _, _ => none
      | _ => none
  | _ => none

def CoreValue.asWordPair? (value : CoreValue) : Option (Word × Word) :=
  match value with
  | SolidCore.Solidity.Source.Value.tuple values =>
      match values with
      | xValue :: yValue :: [] =>
          match xValue, yValue with
          | SolidCore.Solidity.Source.Value.word x,
              SolidCore.Solidity.Source.Value.word y =>
              some (x, y)
          | _, _ => none
      | _ => none
  | _ => none

def CoreExpr.evalWord? (context : CoreContext) (runtime : CoreRuntime)
    (expr : CoreExpr) : Option Word :=
  match SolidCore.Solidity.Source.Expr.eval context runtime expr with
  | Except.ok value => CoreValue.asWord? value
  | Except.error _ => none

def CoreExpr.evalWordInEmptyContext? (expr : CoreExpr) : Option Word :=
  CoreExpr.evalWord?
    SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState
      SolidCore.Solidity.Source.State.empty)
    expr

def CoreCallResult.behavior? : CoreCallResult -> Option Behavior
  | SolidCore.Solidity.Source.CallResult.returned _ [] =>
      some Behavior.stopped
  | SolidCore.Solidity.Source.CallResult.returned _ [value] => do
      let word ← CoreValue.asWord? value
      some (Behavior.returnedWord word)
  | _ => none

def SourceUnit.entryNames? (unit : SourceUnit) :
    Option (Name × Name) :=
  match unit.items with
  | [SourceItem.contract contract] =>
      match contract.items with
      | [ContractItem.function fn] => do
          let functionName ← FunctionDecl.coreName? fn
          some (contract.name, functionName)
      | _ => none
  | _ => none

def SourceUnit.entryBehavior? (fuel : Nat) (unit : SourceUnit) :
    Option Behavior := do
  let (contractName, functionName) ← SourceUnit.entryNames? unit
  let result ←
    SourceUnit.callContract? fuel unit contractName
      (SolidCore.Solidity.Source.CallTarget.name functionName)
      SolidCore.Solidity.Source.State.empty []
  CoreCallResult.behavior? result

def SourceUnit.defaultEntryFuel : Nat := 32

def SourceUnit.defaultEntryBehavior? (unit : SourceUnit) :
    Option Behavior :=
  SourceUnit.entryBehavior? SourceUnit.defaultEntryFuel unit

inductive Semantics : SourceUnit -> Behavior -> Prop where
  | empty {source : SourceUnit} :
      source.items = [] ->
      Semantics source Behavior.stopped
  | entry {source : SourceUnit} {behavior : Behavior} {fuel : Nat} :
      SourceUnit.entryBehavior? fuel source = some behavior ->
      Semantics source behavior

namespace Examples

def uncheckedSub : Stmt :=
  Stmt.unchecked
    (Stmt.returnValues
      (some
        (Expr.binary BinaryOp.sub
          (Expr.literal (Literal.number "2"))
          (Expr.literal (Literal.number "3")))))

def uncheckedSubResult : Option CoreResult :=
  Stmt.eval? 8 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState SolidCore.Solidity.Source.State.empty)
    uncheckedSub

def ternarySkipsRejectedBranch : Stmt :=
  Stmt.returnValues
    (some
      (Expr.ternary
        (Expr.literal (Literal.bool true))
        (Expr.literal (Literal.number "7"))
        (Expr.binary BinaryOp.div
          (Expr.literal (Literal.number "1"))
          (Expr.literal (Literal.number "0")))))

def ternarySkipsRejectedBranchResult : Option CoreResult :=
  Stmt.eval? 8 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState SolidCore.Solidity.Source.State.empty)
    ternarySkipsRejectedBranch

def doWhileRunsBeforeCondition : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "x", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "0")))
    , Stmt.doWhile
        (Stmt.expr
          (Expr.assign (Expr.ident "x") AssignOp.addAssign
            (Expr.literal (Literal.number "1"))))
        (Expr.binary BinaryOp.lt
          (Expr.ident "x")
          (Expr.literal (Literal.number "1")))
    , Stmt.returnValues (some (Expr.ident "x")) ]

def doWhileRunsBeforeConditionResult : Option CoreResult :=
  Stmt.eval? 16 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState SolidCore.Solidity.Source.State.empty)
    doWhileRunsBeforeCondition

def expressionStatementFailure : Stmt :=
  Stmt.expr
    (Expr.binary BinaryOp.div
      (Expr.literal (Literal.number "1"))
      (Expr.literal (Literal.number "0")))

def expressionStatementFailureResult : Option CoreResult :=
  Stmt.eval? 4 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState SolidCore.Solidity.Source.State.empty)
    expressionStatementFailure

def deleteLocalStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "x", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "5")))
    , Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "x"))
    , Stmt.returnValues (some (Expr.ident "x")) ]

def deleteLocalStatementResult : Option CoreResult :=
  Stmt.eval? 8 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState SolidCore.Solidity.Source.State.empty)
    deleteLocalStatement

def incrementStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "x", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "2")))
    , Stmt.expr (Expr.unary UnaryOp.preIncrement (Expr.ident "x"))
    , Stmt.returnValues (some (Expr.ident "x")) ]

def incrementStatementResult : Option CoreResult :=
  Stmt.eval? 8 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState SolidCore.Solidity.Source.State.empty)
    incrementStatement

def incrementExpressionVarDeclStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "x", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "1")))
    , Stmt.varDecl
        [{ name := some "post", ty := some (Ty.uint 256) }]
        (some (Expr.unary UnaryOp.postIncrement (Expr.ident "x")))
    , Stmt.varDecl
        [{ name := some "pre", ty := some (Ty.uint 256) }]
        (some (Expr.unary UnaryOp.preIncrement (Expr.ident "x")))
    , Stmt.returnValues
        (some
          (Expr.tuple
            [ TupleItem.value (Expr.ident "post")
            , TupleItem.value (Expr.ident "pre")
            , TupleItem.value (Expr.ident "x") ])) ]

def incrementExpressionVarDeclMatches : Option Bool := do
  let result ←
    Stmt.eval? 16 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      incrementExpressionVarDeclStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned _
      [ SolidCore.Solidity.Source.Value.word post
      , SolidCore.Solidity.Source.Value.word pre
      , SolidCore.Solidity.Source.Value.word final ] =>
      some (post == 1 && pre == 3 && final == 3)
  | _ => some false

def decrementExpressionVarDeclStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "x", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "3")))
    , Stmt.varDecl
        [{ name := some "post", ty := some (Ty.uint 256) }]
        (some (Expr.unary UnaryOp.postDecrement (Expr.ident "x")))
    , Stmt.varDecl
        [{ name := some "pre", ty := some (Ty.uint 256) }]
        (some (Expr.unary UnaryOp.preDecrement (Expr.ident "x")))
    , Stmt.returnValues
        (some
          (Expr.tuple
            [ TupleItem.value (Expr.ident "post")
            , TupleItem.value (Expr.ident "pre")
            , TupleItem.value (Expr.ident "x") ])) ]

def decrementExpressionVarDeclMatches : Option Bool := do
  let result ←
    Stmt.eval? 16 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      decrementExpressionVarDeclStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned _
      [ SolidCore.Solidity.Source.Value.word post
      , SolidCore.Solidity.Source.Value.word pre
      , SolidCore.Solidity.Source.Value.word final ] =>
      some (post == 3 && pre == 1 && final == 1)
  | _ => some false

def incrementExpressionAssignmentStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "x", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "1")))
    , Stmt.varDecl
        [{ name := some "y", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "0")))
    , Stmt.varDecl
        [{ name := some "z", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "0")))
    , Stmt.expr
        (Expr.assign (Expr.ident "y") AssignOp.assign
          (Expr.binary BinaryOp.add
            (Expr.unary UnaryOp.postIncrement (Expr.ident "x"))
            (Expr.literal (Literal.number "10"))))
    , Stmt.expr
        (Expr.assign (Expr.ident "z") AssignOp.assign
          (Expr.binary BinaryOp.add
            (Expr.unary UnaryOp.preIncrement (Expr.ident "x"))
            (Expr.literal (Literal.number "10"))))
    , Stmt.returnValues
        (some
          (Expr.tuple
            [ TupleItem.value (Expr.ident "y")
            , TupleItem.value (Expr.ident "z")
            , TupleItem.value (Expr.ident "x") ])) ]

def incrementExpressionAssignmentMatches : Option Bool := do
  let result ←
    Stmt.eval? 16 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      incrementExpressionAssignmentStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned _
      [ SolidCore.Solidity.Source.Value.word y
      , SolidCore.Solidity.Source.Value.word z
      , SolidCore.Solidity.Source.Value.word final ] =>
      some (y == 11 && z == 13 && final == 3)
  | _ => some false

def signedIncrementExpressionVarDeclStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "x", ty := some (Ty.int 256) }]
        (some (Expr.literal (Literal.number "1")))
    , Stmt.varDecl
        [{ name := some "post", ty := some (Ty.int 256) }]
        (some (Expr.unary UnaryOp.postIncrement (Expr.ident "x")))
    , Stmt.varDecl
        [{ name := some "pre", ty := some (Ty.int 256) }]
        (some (Expr.unary UnaryOp.preIncrement (Expr.ident "x")))
    , Stmt.returnValues
        (some
          (Expr.tuple
            [ TupleItem.value (Expr.ident "post")
            , TupleItem.value (Expr.ident "pre")
            , TupleItem.value (Expr.ident "x") ])) ]

def signedIncrementExpressionVarDeclMatches : Option Bool := do
  let result ←
    Stmt.eval? 16 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      signedIncrementExpressionVarDeclStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned _
      [ SolidCore.Solidity.Source.Value.int post
      , SolidCore.Solidity.Source.Value.int pre
      , SolidCore.Solidity.Source.Value.int final ] =>
      some (post == 1 && pre == 3 && final == 3)
  | _ => some false

def assignmentExpressionVarDeclStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "x", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "1")))
    , Stmt.varDecl
        [{ name := some "assigned", ty := some (Ty.uint 256) }]
        (some
          (Expr.assign (Expr.ident "x") AssignOp.assign
            (Expr.literal (Literal.number "5"))))
    , Stmt.varDecl
        [{ name := some "compound", ty := some (Ty.uint 256) }]
        (some
          (Expr.assign (Expr.ident "x") AssignOp.addAssign
            (Expr.literal (Literal.number "2"))))
    , Stmt.returnValues
        (some
          (Expr.tuple
            [ TupleItem.value (Expr.ident "assigned")
            , TupleItem.value (Expr.ident "compound")
            , TupleItem.value (Expr.ident "x") ])) ]

def assignmentExpressionVarDeclMatches : Option Bool := do
  let result ←
    Stmt.eval? 16 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      assignmentExpressionVarDeclStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned _
      [ SolidCore.Solidity.Source.Value.word assigned
      , SolidCore.Solidity.Source.Value.word compound
      , SolidCore.Solidity.Source.Value.word final ] =>
      some (assigned == 5 && compound == 7 && final == 7)
  | _ => some false

def assignmentExpressionReturnStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "x", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "1")))
    , Stmt.returnValues
        (some
          (Expr.tuple
            [ TupleItem.value
                (Expr.assign (Expr.ident "x") AssignOp.assign
                  (Expr.literal (Literal.number "9")))
            , TupleItem.value (Expr.ident "x") ])) ]

def assignmentExpressionReturnMatches : Option Bool := do
  let result ←
    Stmt.eval? 16 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      assignmentExpressionReturnStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned _
      [ SolidCore.Solidity.Source.Value.word assigned
      , SolidCore.Solidity.Source.Value.word final ] =>
      some (assigned == 9 && final == 9)
  | _ => some false

def indexedAssignmentTargetEffectsStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "i", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "0")))
    , Stmt.varDecl
        [ { name := some "xs"
            ty := some (Ty.array (Ty.uint 256) (some 2))
            location := some DataLocation.memory } ]
        (some
          (Expr.array
            [ Expr.literal (Literal.number "10")
            , Expr.literal (Literal.number "20") ]))
    , Stmt.expr
        (Expr.assign
          (Expr.index
            (Expr.ident "xs")
            (Expr.unary UnaryOp.postIncrement (Expr.ident "i")))
          AssignOp.assign
          (Expr.literal (Literal.number "99")))
    , Stmt.returnValues
        (some
          (Expr.tuple
            [ TupleItem.value (Expr.ident "i")
            , TupleItem.value
                (Expr.index (Expr.ident "xs")
                  (Expr.literal (Literal.number "0")))
            , TupleItem.value
                (Expr.index (Expr.ident "xs")
                  (Expr.literal (Literal.number "1"))) ])) ]

def indexedAssignmentTargetEffectsMatches : Option Bool := do
  let result ←
    Stmt.eval? 24 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      indexedAssignmentTargetEffectsStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned _
      [ SolidCore.Solidity.Source.Value.word index
      , SolidCore.Solidity.Source.Value.word first
      , SolidCore.Solidity.Source.Value.word second ] =>
      some (index == 1 && first == 99 && second == 20)
  | _ => some false

def indexedCompoundTargetEffectsStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "i", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "0")))
    , Stmt.varDecl
        [ { name := some "xs"
            ty := some (Ty.array (Ty.uint 256) (some 2))
            location := some DataLocation.memory } ]
        (some
          (Expr.array
            [ Expr.literal (Literal.number "10")
            , Expr.literal (Literal.number "20") ]))
    , Stmt.expr
        (Expr.assign
          (Expr.index
            (Expr.ident "xs")
            (Expr.unary UnaryOp.postIncrement (Expr.ident "i")))
          AssignOp.addAssign
          (Expr.literal (Literal.number "7")))
    , Stmt.returnValues
        (some
          (Expr.tuple
            [ TupleItem.value (Expr.ident "i")
            , TupleItem.value
                (Expr.index (Expr.ident "xs")
                  (Expr.literal (Literal.number "0")))
            , TupleItem.value
                (Expr.index (Expr.ident "xs")
                  (Expr.literal (Literal.number "1"))) ])) ]

def indexedCompoundTargetEffectsMatches : Option Bool := do
  let result ←
    Stmt.eval? 24 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      indexedCompoundTargetEffectsStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned _
      [ SolidCore.Solidity.Source.Value.word index
      , SolidCore.Solidity.Source.Value.word first
      , SolidCore.Solidity.Source.Value.word second ] =>
      some (index == 1 && first == 17 && second == 20)
  | _ => some false

def tupleIndexedAssignmentTargetEffectsStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "i", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "0")))
    , Stmt.varDecl
        [ { name := some "xs"
            ty := some (Ty.array (Ty.uint 256) (some 2))
            location := some DataLocation.memory } ]
        (some
          (Expr.array
            [ Expr.literal (Literal.number "10")
            , Expr.literal (Literal.number "20") ]))
    , Stmt.expr
        (Expr.assign
          (Expr.tuple
            [ TupleItem.value
                (Expr.index
                  (Expr.ident "xs")
                  (Expr.unary UnaryOp.postIncrement (Expr.ident "i")))
            , TupleItem.value
                (Expr.index
                  (Expr.ident "xs")
                  (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) ])
          AssignOp.assign
          (Expr.tuple
            [ TupleItem.value (Expr.literal (Literal.number "7"))
            , TupleItem.value (Expr.literal (Literal.number "8")) ]))
    , Stmt.returnValues
        (some
          (Expr.tuple
            [ TupleItem.value (Expr.ident "i")
            , TupleItem.value
                (Expr.index (Expr.ident "xs")
                  (Expr.literal (Literal.number "0")))
            , TupleItem.value
                (Expr.index (Expr.ident "xs")
                  (Expr.literal (Literal.number "1"))) ])) ]

def tupleIndexedAssignmentTargetEffectsMatches : Option Bool := do
  let result ←
    Stmt.eval? 24 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      tupleIndexedAssignmentTargetEffectsStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned _
      [ SolidCore.Solidity.Source.Value.word index
      , SolidCore.Solidity.Source.Value.word first
      , SolidCore.Solidity.Source.Value.word second ] =>
      some (index == 2 && first == 7 && second == 8)
  | _ => some false

def storageIndexedCompoundTargetEffectsContract : ContractDecl :=
  { name := "StorageIndexedCompoundTargetEffects"
    items :=
      [ ContractItem.stateVar
          { name := "items"
            ty := Ty.array (Ty.uint 256) none }
      , ContractItem.function
          { name := some "run"
            returns :=
              [ { name := some "index", ty := Ty.uint 256 }
              , { name := some "first", ty := Ty.uint 256 }
              , { name := some "second", ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "10"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "20"))])
                  , Stmt.varDecl
                      [{ name := some "i", ty := some (Ty.uint 256) }]
                      (some (Expr.literal (Literal.number "0")))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "items")
                          (Expr.unary UnaryOp.postIncrement
                            (Expr.ident "i")))
                        AssignOp.addAssign
                        (Expr.literal (Literal.number "7")))
                  , Stmt.returnValues
                      (some
                        (Expr.tuple
                          [ TupleItem.value (Expr.ident "i")
                          , TupleItem.value
                              (Expr.index (Expr.ident "items")
                                (Expr.literal (Literal.number "0")))
                          , TupleItem.value
                              (Expr.index (Expr.ident "items")
                                (Expr.literal (Literal.number "1"))) ])) ]) } ] }

def storageIndexedCompoundTargetEffectsMatches : Option Bool := do
  let result ←
    ContractDecl.call? 48 storageIndexedCompoundTargetEffectsContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word index
      , SolidCore.Solidity.Source.Value.word first
      , SolidCore.Solidity.Source.Value.word second ] =>
      some (index == 1 && first == 17 && second == 20)
  | _ => some false

def indexedDeleteAndIncrementTargetEffectsStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "i", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "0")))
    , Stmt.varDecl
        [ { name := some "xs"
            ty := some (Ty.array (Ty.uint 256) (some 3))
            location := some DataLocation.memory } ]
        (some
          (Expr.array
            [ Expr.literal (Literal.number "10")
            , Expr.literal (Literal.number "20")
            , Expr.literal (Literal.number "30") ]))
    , Stmt.expr
        (Expr.unary UnaryOp.delete
          (Expr.index
            (Expr.ident "xs")
            (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))))
    , Stmt.varDecl
        [{ name := some "old", ty := some (Ty.uint 256) }]
        (some
          (Expr.unary UnaryOp.postIncrement
            (Expr.index
              (Expr.ident "xs")
              (Expr.unary UnaryOp.postIncrement (Expr.ident "i")))))
    , Stmt.returnValues
        (some
          (Expr.tuple
            [ TupleItem.value (Expr.ident "old")
            , TupleItem.value (Expr.ident "i")
            , TupleItem.value
                (Expr.index (Expr.ident "xs")
                  (Expr.literal (Literal.number "0")))
            , TupleItem.value
                (Expr.index (Expr.ident "xs")
                  (Expr.literal (Literal.number "1")))
            , TupleItem.value
                (Expr.index (Expr.ident "xs")
                  (Expr.literal (Literal.number "2"))) ])) ]

def indexedDeleteAndIncrementTargetEffectsMatches : Option Bool := do
  let result ←
    Stmt.eval? 32 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      indexedDeleteAndIncrementTargetEffectsStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned _
      [ SolidCore.Solidity.Source.Value.word old
      , SolidCore.Solidity.Source.Value.word index
      , SolidCore.Solidity.Source.Value.word first
      , SolidCore.Solidity.Source.Value.word second
      , SolidCore.Solidity.Source.Value.word third ] =>
      some
        (old == 20 && index == 2 && first == 0 && second == 21 &&
          third == 30)
  | _ => some false

def requireCustomArgumentEvaluationStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "x", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "1")))
    , Stmt.expr
        (Expr.call (Expr.ident "require")
          [ Arg.positional (Expr.literal (Literal.bool true))
          , Arg.positional
              (Expr.call (Expr.ident "NeedsEval")
                [Arg.positional
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.literal (Literal.number "5")))]) ])
    , Stmt.returnValues (some (Expr.ident "x")) ]

def requireCustomArgumentEvaluationMatches : Option Bool := do
  let result ←
    Stmt.eval? 16 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      requireCustomArgumentEvaluationStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned _
      [SolidCore.Solidity.Source.Value.word final] =>
      some (final == 5)
  | _ => some false

def tryExternalCallOperandEffectsStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "target", ty := some (Ty.address false) }]
        (some (Expr.literal (Literal.number "0")))
    , Stmt.varDecl
        [{ name := some "value", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "0")))
    , Stmt.varDecl
        [{ name := some "arg", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "0")))
    , Stmt.tryCatchReturns
        (Expr.callWithOptions
          (Expr.member
            (Expr.assign (Expr.ident "target") AssignOp.assign
              (Expr.literal (Literal.number "51966")))
            "ping")
          [ CallOption.named "value"
              (Expr.assign (Expr.ident "value") AssignOp.assign
                (Expr.literal (Literal.number "7"))) ]
          [ Arg.positional
              (Expr.call (Expr.typeName (Ty.uint 256))
                [Arg.positional
                  (Expr.assign (Expr.ident "arg") AssignOp.assign
                    (Expr.literal (Literal.number "3")))]) ])
        [{ name := some "out", ty := Ty.uint 256 }]
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value (Expr.ident "target")
              , TupleItem.value (Expr.ident "value")
              , TupleItem.value (Expr.ident "arg")
              , TupleItem.value (Expr.ident "out") ])))
        [CatchClause.clause none [] (Stmt.returnValues none)] ]

def tryExternalCallOperandEffectsContext? : Option CoreContext := do
  let calldataArgs ←
    SolidCore.Solidity.Source.abiEncodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 3]
  let output ←
    SolidCore.Solidity.Source.abiEncodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 99]
  let selector :=
    SolidCore.Solidity.Source.ABI.selectorFromSignature "ping(uint256)"
  let calldata :=
    SolidCore.Solidity.Source.wordToBytesBE
      SolidCore.Solidity.Source.selectorBytes selector ++ calldataArgs
  some
    { SolidCore.Solidity.Source.Context.empty with
      lowLevelCallResults :=
        [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
            target := 51966
            calldata := calldata
            value := 7
            success := true
            output := output } ] }

def tryExternalCallOperandEffectsMatches : Option Bool := do
  let context ← tryExternalCallOperandEffectsContext?
  let result ←
    Stmt.eval? 32 [] context
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      tryExternalCallOperandEffectsStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned _
      [ SolidCore.Solidity.Source.Value.word target
      , SolidCore.Solidity.Source.Value.word value
      , SolidCore.Solidity.Source.Value.word arg
      , SolidCore.Solidity.Source.Value.word out ] =>
      some (target == 51966 && value == 7 && arg == 3 && out == 99)
  | _ => some false

def tryContractCreateOperandEffectsStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "value", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "0")))
    , Stmt.varDecl
        [{ name := some "salt", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "0")))
    , Stmt.varDecl
        [{ name := some "arg", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "0")))
    , Stmt.tryCatchReturns
        (Expr.callWithOptions
          (Expr.newExpr (Ty.user { segments := ["Made"] }) [])
          [ CallOption.named "value"
              (Expr.assign (Expr.ident "value") AssignOp.assign
                (Expr.literal (Literal.number "7")))
          , CallOption.named "salt"
              (Expr.assign (Expr.ident "salt") AssignOp.assign
                (Expr.literal (Literal.number "5"))) ]
          [ Arg.positional
              (Expr.call (Expr.typeName (Ty.uint 256))
                [Arg.positional
                  (Expr.assign (Expr.ident "arg") AssignOp.assign
                    (Expr.literal (Literal.number "3")))]) ])
        [{ name := some "made", ty := Ty.address false }]
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value (Expr.ident "value")
              , TupleItem.value (Expr.ident "salt")
              , TupleItem.value (Expr.ident "arg")
              , TupleItem.value (Expr.ident "made") ])))
        [CatchClause.clause none [] (Stmt.returnValues none)] ]

def tryContractCreateOperandEffectsContext? : Option CoreContext := do
  let constructorArgs ←
    SolidCore.Solidity.Source.abiEncodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 3]
  some
    { SolidCore.Solidity.Source.Context.empty with
      contractCreationResults :=
        [ { contractName := "Made"
            constructorArgs := constructorArgs
            value := 7
            salt? := some 5
            success := true
            address := 51966
            output := [] } ] }

def tryContractCreateOperandEffectsMatches : Option Bool := do
  let context ← tryContractCreateOperandEffectsContext?
  let result ←
    Stmt.eval? 32 [] context
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      tryContractCreateOperandEffectsStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned _
      [ SolidCore.Solidity.Source.Value.word value
      , SolidCore.Solidity.Source.Value.word salt
      , SolidCore.Solidity.Source.Value.word arg
      , SolidCore.Solidity.Source.Value.word made ] =>
      some (value == 7 && salt == 5 && arg == 3 && made == 51966)
  | _ => some false

def eventArgumentEvaluationStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "x", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "1")))
    , Stmt.emitEvent
        (Expr.call (Expr.ident "Seen")
          [Arg.positional
            (Expr.assign (Expr.ident "x") AssignOp.assign
              (Expr.literal (Literal.number "5")))])
    , Stmt.returnValues (some (Expr.ident "x")) ]

def eventArgumentEvaluationContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    eventDecls :=
      [ { name := "Seen"
          indexedCount := 0 } ] }

def eventArgumentEvaluationMatches : Option Bool := do
  let result ←
    Stmt.eval? 16 [] eventArgumentEvaluationContext
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      eventArgumentEvaluationStatement
  match result with
  | SolidCore.Solidity.Source.Result.returned runtime
      [SolidCore.Solidity.Source.Value.word final] =>
      match runtime.state.events with
      | [{ name := "Seen"
           data := [SolidCore.Solidity.Source.Value.word emitted]
           .. }] =>
          some (final == 5 && emitted == 5)
      | _ => some false
  | _ => some false

def revertCustomArgumentEvaluationStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "x", ty := some (Ty.uint 256) }]
        (some (Expr.literal (Literal.number "1")))
    , Stmt.revertCall
        (Expr.call (Expr.ident "NeedsEval")
          [Arg.positional
            (Expr.assign (Expr.ident "x") AssignOp.assign
              (Expr.literal (Literal.number "5")))]) ]

def revertCustomArgumentEvaluationMatches : Option Bool := do
  let result ←
    Stmt.eval? 16 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      revertCustomArgumentEvaluationStatement
  match result with
  | SolidCore.Solidity.Source.Result.reverted _
      (SolidCore.Solidity.Source.RevertData.custom "NeedsEval"
        [SolidCore.Solidity.Source.Value.word arg]) =>
      some (arg == 5)
  | _ => some false

def boolIdentityFunction : FunctionDecl :=
  { name := some "idBool"
    params := [{ name := some "value", ty := Ty.bool }]
    returns := [{ name := some "out", ty := Ty.bool }]
    body := some (Stmt.returnValues (some (Expr.ident "value"))) }

def boolIdentityCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty boolIdentityFunction
    [SolidCore.Solidity.Source.Value.word 1]

def addressIdentityFunction : FunctionDecl :=
  { name := some "idAddress"
    params := [{ name := some "value", ty := Ty.address false }]
    returns := [{ name := some "out", ty := Ty.address false }]
    body := some (Stmt.returnValues (some (Expr.ident "value"))) }

def addressIdentityCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty addressIdentityFunction
    [SolidCore.Solidity.Source.Value.word 0x1234]

def assertFailureStatement : Stmt :=
  Stmt.expr
    (Expr.call (Expr.ident "assert")
      [Arg.positional (Expr.literal (Literal.bool false))])

def assertFailureStatementResult : Option CoreResult :=
  Stmt.eval? 4 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState SolidCore.Solidity.Source.State.empty)
    assertFailureStatement

def requireFailureStatement : Stmt :=
  Stmt.expr
    (Expr.call (Expr.ident "require")
      [ Arg.positional (Expr.literal (Literal.bool false))
      , Arg.positional (Expr.literal (Literal.string "Nope")) ])

def requireFailureStatementResult : Option CoreResult :=
  Stmt.eval? 4 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState SolidCore.Solidity.Source.State.empty)
    requireFailureStatement

def revertStringStatement : Stmt :=
  Stmt.revertCall
    (Expr.call (Expr.ident "revert")
      [Arg.positional (Expr.literal (Literal.string "Nope"))])

def revertStringStatementResult : Option CoreResult :=
  Stmt.eval? 4 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState SolidCore.Solidity.Source.State.empty)
    revertStringStatement

def errorStringBytes? (text : String) : Option (List Byte) := do
  let encoded ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.bytesCalldata]
      [SolidCore.Solidity.Source.Value.bytes
        (text.toList.map Char.toNat)]
  some
    (SolidCore.Solidity.Source.ABI.encodeSelector
      SolidCore.Solidity.Source.ABI.errorSelector ++ encoded)

def dynamicRequireReasonStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "reason", ty := some Ty.string }]
        (some (Expr.literal (Literal.string "Nope")))
    , Stmt.expr
        (Expr.call (Expr.ident "require")
          [ Arg.positional (Expr.literal (Literal.bool false))
          , Arg.positional (Expr.ident "reason") ]) ]

def dynamicRequireReasonMatches : Option Bool := do
  let expected ← errorStringBytes? "Nope"
  let result ←
    Stmt.eval? 8 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      dynamicRequireReasonStatement
  match result with
  | SolidCore.Solidity.Source.Result.reverted _
      (SolidCore.Solidity.Source.RevertData.raw bytes) =>
      some (bytes == expected)
  | _ => some false

def dynamicRevertReasonStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "reason", ty := some Ty.string }]
        (some (Expr.literal (Literal.string "Gone")))
    , Stmt.revertCall
        (Expr.call (Expr.ident "revert")
          [Arg.positional (Expr.ident "reason")]) ]

def dynamicRevertReasonMatches : Option Bool := do
  let expected ← errorStringBytes? "Gone"
  let result ←
    Stmt.eval? 8 [] SolidCore.Solidity.Source.Context.empty
      (SolidCore.Solidity.Source.Runtime.ofState
        SolidCore.Solidity.Source.State.empty)
      dynamicRevertReasonStatement
  match result with
  | SolidCore.Solidity.Source.Result.reverted _
      (SolidCore.Solidity.Source.RevertData.raw bytes) =>
      some (bytes == expected)
  | _ => some false

def publicGetterContract : ContractDecl :=
  { name := "Getter"
    items :=
      [ ContractItem.stateVar
          { name := "x"
            ty := Ty.uint 256
            visibility := some Visibility.public_ } ] }

def publicGetterState : CoreState :=
  SolidCore.Solidity.Source.State.storeSlot
    SolidCore.Solidity.Source.State.empty 0 42

def publicGetterCallResult : Option CoreCallResult :=
  ContractDecl.call? 8 publicGetterContract
    (SolidCore.Solidity.Source.CallTarget.name "x")
    publicGetterState []

def publicGetterCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? publicGetterContract
  let function ← contract.findFunctionByName? "x"
  let calldata ← SolidCore.Solidity.Source.ABI.calldataFor? function []
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    8 contract publicGetterState calldata

def abiCallableFunction : FunctionDecl :=
  { name := some "pick"
    params :=
      [ { name := some "value", ty := Ty.uint 256 }
      , { name := some "flag", ty := Ty.bool } ]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.ternary
              (Expr.ident "flag")
              (Expr.ident "value")
              (Expr.literal (Literal.number "0"))))) }

def abiCallableContract : ContractDecl :=
  { name := "Abi"
    items := [ContractItem.function abiCallableFunction] }

def abiCallableCalldata : Option (List Byte) := do
  let contract ← ContractDecl.toCore? abiCallableContract
  let function ← contract.findFunctionByName? "pick"
  SolidCore.Solidity.Source.ABI.calldataFor? function
    [ SolidCore.Solidity.Source.Value.word 42
    , SolidCore.Solidity.Source.Value.word 1 ]

def abiCallableCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? abiCallableContract
  let calldata ← abiCallableCalldata
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract SolidCore.Solidity.Source.State.empty calldata

def fixedArrayAbiFunction : FunctionDecl :=
  { name := some "sumPair"
    params :=
      [ { name := some "pair", ty := Ty.array (Ty.uint 256) (some 2) }
      , { name := some "flag", ty := Ty.bool } ]
    returns :=
      [ { name := some "sum", ty := Ty.uint 256 }
      , { name := some "echo", ty := Ty.array (Ty.uint 256) (some 2) } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.binary BinaryOp.add
                    (Expr.binary BinaryOp.add
                      (Expr.index (Expr.ident "pair")
                        (Expr.literal (Literal.number "0")))
                      (Expr.index (Expr.ident "pair")
                        (Expr.literal (Literal.number "1"))))
                    (Expr.ternary
                      (Expr.ident "flag")
                      (Expr.literal (Literal.number "1"))
                      (Expr.literal (Literal.number "0"))))
              , TupleItem.value (Expr.ident "pair") ]))) }

def fixedArrayAbiContract : ContractDecl :=
  { name := "FixedArrayAbi"
    items := [ContractItem.function fixedArrayAbiFunction] }

def fixedArrayAbiCalldata : Option (List Byte) := do
  let contract ← ContractDecl.toCore? fixedArrayAbiContract
  let function ← contract.findFunctionByName? "sumPair"
  SolidCore.Solidity.Source.ABI.calldataFor? function
    [ SolidCore.Solidity.Source.Value.fixedArray
        [ SolidCore.Solidity.Source.Value.word 5
        , SolidCore.Solidity.Source.Value.word 7 ]
    , SolidCore.Solidity.Source.Value.word 1 ]

def fixedArrayAbiDecodedArgs : Option (List CoreValue) := do
  let calldata ← fixedArrayAbiCalldata
  SolidCore.Solidity.Source.ABI.decodeArgs?
    [ SolidCore.Solidity.Source.Ty.fixedArray 2
        SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.bool ]
    (calldata.drop SolidCore.Solidity.Source.ABI.selectorBytes)

def fixedArrayAbiExpectedOutput : Option (List Byte) :=
  SolidCore.Solidity.Source.ABI.encodeValues?
    [ SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.fixedArray 2
        SolidCore.Solidity.Source.Ty.uint256 ]
    [ SolidCore.Solidity.Source.Value.word 13
    , SolidCore.Solidity.Source.Value.fixedArray
        [ SolidCore.Solidity.Source.Value.word 5
        , SolidCore.Solidity.Source.Value.word 7 ] ]

def fixedArrayAbiCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? fixedArrayAbiContract
  let calldata ← fixedArrayAbiCalldata
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract SolidCore.Solidity.Source.State.empty calldata

def fixedArrayAbiOutputMatchesExpected : Option Bool := do
  let result ← fixedArrayAbiCalldataResult
  let expected ← fixedArrayAbiExpectedOutput
  some (result.success && result.output == expected)

def arrayLiteralLocalFunction : FunctionDecl :=
  { name := some "middle"
    params := []
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [ { name := some "xs"
                  ty := some (Ty.array (Ty.uint 256) (some 3))
                  location := some DataLocation.memory } ]
              (some
                (Expr.array
                  [ Expr.literal (Literal.number "1")
                  , Expr.literal (Literal.number "2")
                  , Expr.literal (Literal.number "3") ]))
          , Stmt.expr
              (Expr.assign
                (Expr.index (Expr.ident "xs")
                  (Expr.literal (Literal.number "1")))
                AssignOp.assign
                (Expr.literal (Literal.number "9")))
          , Stmt.returnValues
              (some
                (Expr.index (Expr.ident "xs")
                  (Expr.literal (Literal.number "1")))) ]) }

def arrayLiteralLocalCallResult : Option CoreCallResult :=
  FunctionDecl.call? 16 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty arrayLiteralLocalFunction []

def arrayLiteralLocalMatchesExpected : Option Bool := do
  let result ← arrayLiteralLocalCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value with
      | SolidCore.Solidity.Source.Value.word word => some (word == 9)
      | _ => some false
  | _ => some false

def arrayLiteralAbiEncodeFunction : FunctionDecl :=
  { name := some "encodeArrayLiteral"
    params := []
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.member (Expr.ident "abi") "encode")
              [ Arg.positional
                  (Expr.array
                    [ Expr.literal (Literal.number "1")
                    , Expr.literal (Literal.number "2")
                    , Expr.literal (Literal.number "3") ]) ]))) }

def arrayLiteralAbiEncodeExpected : Option (List Byte) :=
  SolidCore.Solidity.Source.ABI.encodeValues?
    [ SolidCore.Solidity.Source.Ty.fixedArray 3
        SolidCore.Solidity.Source.Ty.uint256 ]
    [ SolidCore.Solidity.Source.Value.fixedArray
        [ SolidCore.Solidity.Source.Value.word 1
        , SolidCore.Solidity.Source.Value.word 2
        , SolidCore.Solidity.Source.Value.word 3 ] ]

def arrayLiteralAbiEncodeCallResult : Option CoreCallResult :=
  FunctionDecl.call? 16 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty arrayLiteralAbiEncodeFunction []

def arrayLiteralAbiEncodeMatchesExpected : Option Bool := do
  let result ← arrayLiteralAbiEncodeCallResult
  let expected ← arrayLiteralAbiEncodeExpected
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value with
      | SolidCore.Solidity.Source.Value.bytes bytes =>
          some (bytes == expected)
      | _ => some false
  | _ => some false

def memoryArrayAllocationFunction : FunctionDecl :=
  { name := some "allocate"
    params := [{ name := some "len", ty := Ty.uint 256 }]
    returns :=
      [ { name := some "arrayLength", ty := Ty.uint 256 }
      , { name := some "defaultFirst", ty := Ty.uint 256 }
      , { name := some "updatedMiddle", ty := Ty.uint 256 }
      , { name := some "defaultLast", ty := Ty.uint 256 } ]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [ { name := some "xs"
                  ty := some (Ty.array (Ty.uint 256) none)
                  location := some DataLocation.memory } ]
              (some
                (Expr.newExpr (Ty.array (Ty.uint 256) none)
                  [Arg.positional (Expr.ident "len")]))
          , Stmt.expr
              (Expr.assign
                (Expr.index (Expr.ident "xs")
                  (Expr.literal (Literal.number "1")))
                AssignOp.assign
                (Expr.literal (Literal.number "7")))
          , Stmt.returnValues
              (some
                (Expr.tuple
                  [ TupleItem.value
                      (Expr.member (Expr.ident "xs") "length")
                  , TupleItem.value
                      (Expr.index (Expr.ident "xs")
                        (Expr.literal (Literal.number "0")))
                  , TupleItem.value
                      (Expr.index (Expr.ident "xs")
                        (Expr.literal (Literal.number "1")))
                  , TupleItem.value
                      (Expr.index (Expr.ident "xs")
                        (Expr.literal (Literal.number "2"))) ])) ]) }

def memoryArrayAllocationCallResult : Option CoreCallResult :=
  FunctionDecl.call? 16 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty memoryArrayAllocationFunction
    [SolidCore.Solidity.Source.Value.word 3]

def memoryArrayAllocationMatchesExpected : Option Bool := do
  let result ← memoryArrayAllocationCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word arrayLength
      , SolidCore.Solidity.Source.Value.word defaultFirst
      , SolidCore.Solidity.Source.Value.word updatedMiddle
      , SolidCore.Solidity.Source.Value.word defaultLast ] =>
      some (arrayLength == 3 &&
        defaultFirst == 0 &&
        updatedMiddle == 7 &&
        defaultLast == 0)
  | _ => some false

def memoryArrayAllocationOutOfBoundsPanics : Option Bool := do
  let result ←
    FunctionDecl.call? 16 [] [] SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty memoryArrayAllocationFunction
      [SolidCore.Solidity.Source.Value.word 1]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      some (code == 0x32)
  | _ => some false

def memoryArrayAllocationRejected : Bool :=
  (match
      Expr.toCore? []
        (Expr.newExpr (Ty.array (Ty.uint 256) (some 3))
          [Arg.positional (Expr.literal (Literal.number "3"))])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.newExpr (Ty.array (Ty.uint 256) none) [])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.newExpr (Ty.array (Ty.uint 256) none)
          [ Arg.positional (Expr.literal (Literal.number "3"))
          , Arg.positional (Expr.literal (Literal.number "4")) ])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.newExpr
          (Ty.array (Ty.mapping (Ty.uint 256) (Ty.uint 256)) none)
          [Arg.positional (Expr.literal (Literal.number "1"))])
    with
    | none => true
    | some _ => false)

def memoryBytesAllocationFunction : FunctionDecl :=
  { name := some "allocateBytes"
    params := [{ name := some "len", ty := Ty.uint 256 }]
    returns :=
      [ { name := some "data", ty := Ty.bytes }
      , { name := some "byteLength", ty := Ty.uint 256 }
      , { name := some "defaultFirst", ty := Ty.uint 256 }
      , { name := some "updatedMiddle", ty := Ty.uint 256 }
      , { name := some "defaultLast", ty := Ty.uint 256 } ]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [ { name := some "buf"
                  ty := some Ty.bytes
                  location := some DataLocation.memory } ]
              (some
                (Expr.newExpr Ty.bytes
                  [Arg.positional (Expr.ident "len")]))
          , Stmt.expr
              (Expr.assign
                (Expr.index (Expr.ident "buf")
                  (Expr.literal (Literal.number "1")))
                AssignOp.assign
                (Expr.call (Expr.typeName (Ty.bytesN 1))
                  [Arg.positional
                    (Expr.literal (Literal.number "0xab"))]))
          , Stmt.returnValues
              (some
                (Expr.tuple
                  [ TupleItem.value (Expr.ident "buf")
                  , TupleItem.value
                      (Expr.member (Expr.ident "buf") "length")
                  , TupleItem.value
                      (Expr.index (Expr.ident "buf")
                        (Expr.literal (Literal.number "0")))
                  , TupleItem.value
                      (Expr.index (Expr.ident "buf")
                        (Expr.literal (Literal.number "1")))
                  , TupleItem.value
                      (Expr.index (Expr.ident "buf")
                        (Expr.literal (Literal.number "2"))) ])) ]) }

def memoryBytesAllocationCallResult : Option CoreCallResult :=
  FunctionDecl.call? 16 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty memoryBytesAllocationFunction
    [SolidCore.Solidity.Source.Value.word 3]

def memoryBytesAllocationMatchesExpected : Option Bool := do
  let result ← memoryBytesAllocationCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.bytes data
      , SolidCore.Solidity.Source.Value.word byteLength
      , SolidCore.Solidity.Source.Value.word defaultFirst
      , SolidCore.Solidity.Source.Value.word updatedMiddle
      , SolidCore.Solidity.Source.Value.word defaultLast ] =>
      some (data == [0, 0xab, 0] &&
        byteLength == 3 &&
        defaultFirst == 0 &&
        updatedMiddle == 0xab &&
        defaultLast == 0)
  | _ => some false

def memoryBytesAllocationOutOfBoundsPanics : Option Bool := do
  let result ←
    FunctionDecl.call? 16 [] [] SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty memoryBytesAllocationFunction
      [SolidCore.Solidity.Source.Value.word 1]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      some (code == 0x32)
  | _ => some false

def memoryBytesAllocationRejected : Bool :=
  (match
      Expr.toCore? []
        (Expr.newExpr Ty.bytes [])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.newExpr Ty.bytes
          [ Arg.positional (Expr.literal (Literal.number "3"))
          , Arg.positional (Expr.literal (Literal.number "4")) ])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.newExpr Ty.string
          [Arg.positional (Expr.literal (Literal.number "3"))])
    with
    | none => true
    | some _ => false)

def fixedArrayThenBytesAbiFunction : FunctionDecl :=
  { name := some "arrayThenBytes"
    params :=
      [ { name := some "pair", ty := Ty.array (Ty.uint 256) (some 2) }
      , { name := some "payload", ty := Ty.bytes } ]
    returns :=
      [ { name := some "second", ty := Ty.uint 256 }
      , { name := some "payloadLength", ty := Ty.uint 256 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.index (Expr.ident "pair")
                    (Expr.literal (Literal.number "1")))
              , TupleItem.value
                  (Expr.member (Expr.ident "payload") "length") ]))) }

def fixedArrayThenBytesAbiContract : ContractDecl :=
  { name := "FixedArrayThenBytesAbi"
    items := [ContractItem.function fixedArrayThenBytesAbiFunction] }

def fixedArrayThenBytesAbiCalldata : Option (List Byte) := do
  let contract ← ContractDecl.toCore? fixedArrayThenBytesAbiContract
  let function ← contract.findFunctionByName? "arrayThenBytes"
  SolidCore.Solidity.Source.ABI.calldataFor? function
    [ SolidCore.Solidity.Source.Value.fixedArray
        [ SolidCore.Solidity.Source.Value.word 9
        , SolidCore.Solidity.Source.Value.word 10 ]
    , SolidCore.Solidity.Source.Value.bytes [1, 2, 3] ]

def fixedArrayThenBytesAbiExpectedOutput : Option (List Byte) :=
  SolidCore.Solidity.Source.ABI.encodeValues?
    [ SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.uint256 ]
    [ SolidCore.Solidity.Source.Value.word 10
    , SolidCore.Solidity.Source.Value.word 3 ]

def fixedArrayThenBytesAbiCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? fixedArrayThenBytesAbiContract
  let calldata ← fixedArrayThenBytesAbiCalldata
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract SolidCore.Solidity.Source.State.empty calldata

def fixedArrayThenBytesAbiOutputMatchesExpected : Option Bool := do
  let result ← fixedArrayThenBytesAbiCalldataResult
  let expected ← fixedArrayThenBytesAbiExpectedOutput
  some (result.success && result.output == expected)

def dynamicFixedArrayAbiFunction : FunctionDecl :=
  { name := some "bytesPair"
    params :=
      [ { name := some "pair"
          ty := Ty.array Ty.bytes (some 2)
          location := some DataLocation.calldata }
      , { name := some "flag", ty := Ty.bool } ]
    returns :=
      [ { name := some "total", ty := Ty.uint 256 }
      , { name := some "echo"
          ty := Ty.array Ty.bytes (some 2)
          location := some DataLocation.memory } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.binary BinaryOp.add
                    (Expr.binary BinaryOp.add
                      (Expr.member
                        (Expr.index (Expr.ident "pair")
                          (Expr.literal (Literal.number "0")))
                        "length")
                      (Expr.member
                        (Expr.index (Expr.ident "pair")
                          (Expr.literal (Literal.number "1")))
                        "length"))
                    (Expr.ternary
                      (Expr.ident "flag")
                      (Expr.literal (Literal.number "1"))
                      (Expr.literal (Literal.number "0"))))
              , TupleItem.value (Expr.ident "pair") ]))) }

def dynamicFixedArrayAbiContract : ContractDecl :=
  { name := "DynamicFixedArrayAbi"
    items := [ContractItem.function dynamicFixedArrayAbiFunction] }

def dynamicFixedArrayAbiValue : CoreValue :=
  SolidCore.Solidity.Source.Value.fixedArray
    [ SolidCore.Solidity.Source.Value.bytes [1, 2]
    , SolidCore.Solidity.Source.Value.bytes [3, 4, 5] ]

def dynamicFixedArrayAbiCalldata : Option (List Byte) := do
  let contract ← ContractDecl.toCore? dynamicFixedArrayAbiContract
  let function ← contract.findFunctionByName? "bytesPair"
  SolidCore.Solidity.Source.ABI.calldataFor? function
    [ dynamicFixedArrayAbiValue
    , SolidCore.Solidity.Source.Value.word 1 ]

def dynamicFixedArrayAbiDecodedArgs : Option (List CoreValue) := do
  let calldata ← dynamicFixedArrayAbiCalldata
  SolidCore.Solidity.Source.ABI.decodeArgs?
    [ SolidCore.Solidity.Source.Ty.fixedArray 2
        SolidCore.Solidity.Source.Ty.bytesCalldata
    , SolidCore.Solidity.Source.Ty.bool ]
    (calldata.drop SolidCore.Solidity.Source.ABI.selectorBytes)

def dynamicFixedArrayAbiExpectedOutput : Option (List Byte) :=
  SolidCore.Solidity.Source.ABI.encodeValues?
    [ SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.fixedArray 2
        SolidCore.Solidity.Source.Ty.bytesCalldata ]
    [ SolidCore.Solidity.Source.Value.word 6
    , dynamicFixedArrayAbiValue ]

def dynamicFixedArrayAbiCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? dynamicFixedArrayAbiContract
  let calldata ← dynamicFixedArrayAbiCalldata
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    32 contract SolidCore.Solidity.Source.State.empty calldata

def dynamicFixedArrayAbiOutputMatchesExpected : Option Bool := do
  let result ← dynamicFixedArrayAbiCalldataResult
  let expected ← dynamicFixedArrayAbiExpectedOutput
  some (result.success && result.output == expected)

def staticTupleAbiFunction : FunctionDecl :=
  { name := some "staticTuple"
    params :=
      [ { name := some "bundle"
          ty := Ty.tuple [Ty.uint 256, Ty.bool] }
      , { name := some "tail", ty := Ty.uint 256 } ]
    returns :=
      [ { name := some "total", ty := Ty.uint 256 }
      , { name := some "echo"
          ty := Ty.tuple [Ty.uint 256, Ty.bool] } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.binary BinaryOp.add
                    (Expr.binary BinaryOp.add
                      (Expr.index (Expr.ident "bundle")
                        (Expr.literal (Literal.number "0")))
                      (Expr.ternary
                        (Expr.index (Expr.ident "bundle")
                          (Expr.literal (Literal.number "1")))
                        (Expr.literal (Literal.number "1"))
                        (Expr.literal (Literal.number "0"))))
                    (Expr.ident "tail"))
              , TupleItem.value (Expr.ident "bundle") ]))) }

def staticTupleAbiContract : ContractDecl :=
  { name := "StaticTupleAbi"
    items := [ContractItem.function staticTupleAbiFunction] }

def staticTupleAbiValue : CoreValue :=
  SolidCore.Solidity.Source.Value.tuple
    [ SolidCore.Solidity.Source.Value.word 20
    , SolidCore.Solidity.Source.Value.word 1 ]

def staticTupleAbiCalldata : Option (List Byte) := do
  let contract ← ContractDecl.toCore? staticTupleAbiContract
  let function ← contract.findFunctionByName? "staticTuple"
  SolidCore.Solidity.Source.ABI.calldataFor? function
    [ staticTupleAbiValue
    , SolidCore.Solidity.Source.Value.word 5 ]

def staticTupleAbiDecodedArgs : Option (List CoreValue) := do
  let calldata ← staticTupleAbiCalldata
  SolidCore.Solidity.Source.ABI.decodeArgs?
    [ SolidCore.Solidity.Source.Ty.tuple
        [ SolidCore.Solidity.Source.Ty.uint256
        , SolidCore.Solidity.Source.Ty.bool ]
    , SolidCore.Solidity.Source.Ty.uint256 ]
    (calldata.drop SolidCore.Solidity.Source.ABI.selectorBytes)

def staticTupleAbiExpectedOutput : Option (List Byte) :=
  SolidCore.Solidity.Source.ABI.encodeValues?
    [ SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.tuple
        [ SolidCore.Solidity.Source.Ty.uint256
        , SolidCore.Solidity.Source.Ty.bool ] ]
    [ SolidCore.Solidity.Source.Value.word 26
    , staticTupleAbiValue ]

def staticTupleAbiCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? staticTupleAbiContract
  let calldata ← staticTupleAbiCalldata
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract SolidCore.Solidity.Source.State.empty calldata

def staticTupleAbiOutputMatchesExpected : Option Bool := do
  let result ← staticTupleAbiCalldataResult
  let expected ← staticTupleAbiExpectedOutput
  some (result.success && result.output == expected)

def dynamicTupleAbiFunction : FunctionDecl :=
  { name := some "dynamicTuple"
    params :=
      [ { name := some "bundle"
          ty := Ty.tuple [Ty.uint 256, Ty.bytes]
          location := some DataLocation.calldata }
      , { name := some "flag", ty := Ty.bool } ]
    returns :=
      [ { name := some "total", ty := Ty.uint 256 }
      , { name := some "echo"
          ty := Ty.tuple [Ty.uint 256, Ty.bytes]
          location := some DataLocation.memory } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.binary BinaryOp.add
                    (Expr.binary BinaryOp.add
                      (Expr.index (Expr.ident "bundle")
                        (Expr.literal (Literal.number "0")))
                      (Expr.member
                        (Expr.index (Expr.ident "bundle")
                          (Expr.literal (Literal.number "1")))
                        "length"))
                    (Expr.ternary
                      (Expr.ident "flag")
                      (Expr.literal (Literal.number "1"))
                      (Expr.literal (Literal.number "0"))))
              , TupleItem.value (Expr.ident "bundle") ]))) }

def dynamicTupleAbiContract : ContractDecl :=
  { name := "DynamicTupleAbi"
    items := [ContractItem.function dynamicTupleAbiFunction] }

def dynamicTupleAbiValue : CoreValue :=
  SolidCore.Solidity.Source.Value.tuple
    [ SolidCore.Solidity.Source.Value.word 40
    , SolidCore.Solidity.Source.Value.bytes [1, 2, 3] ]

def dynamicTupleAbiCalldata : Option (List Byte) := do
  let contract ← ContractDecl.toCore? dynamicTupleAbiContract
  let function ← contract.findFunctionByName? "dynamicTuple"
  SolidCore.Solidity.Source.ABI.calldataFor? function
    [ dynamicTupleAbiValue
    , SolidCore.Solidity.Source.Value.word 1 ]

def dynamicTupleAbiDecodedArgs : Option (List CoreValue) := do
  let calldata ← dynamicTupleAbiCalldata
  SolidCore.Solidity.Source.ABI.decodeArgs?
    [ SolidCore.Solidity.Source.Ty.tuple
        [ SolidCore.Solidity.Source.Ty.uint256
        , SolidCore.Solidity.Source.Ty.bytesCalldata ]
    , SolidCore.Solidity.Source.Ty.bool ]
    (calldata.drop SolidCore.Solidity.Source.ABI.selectorBytes)

def dynamicTupleAbiExpectedOutput : Option (List Byte) :=
  SolidCore.Solidity.Source.ABI.encodeValues?
    [ SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.tuple
        [ SolidCore.Solidity.Source.Ty.uint256
        , SolidCore.Solidity.Source.Ty.bytesCalldata ] ]
    [ SolidCore.Solidity.Source.Value.word 44
    , dynamicTupleAbiValue ]

def dynamicTupleAbiCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? dynamicTupleAbiContract
  let calldata ← dynamicTupleAbiCalldata
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    24 contract SolidCore.Solidity.Source.State.empty calldata

def dynamicTupleAbiOutputMatchesExpected : Option Bool := do
  let result ← dynamicTupleAbiCalldataResult
  let expected ← dynamicTupleAbiExpectedOutput
  some (result.success && result.output == expected)

def dynamicArrayAbiFunction : FunctionDecl :=
  { name := some "arrayInfo"
    params :=
      [ { name := some "items"
          ty := Ty.array (Ty.uint 256) none
          location := some DataLocation.calldata }
      , { name := some "flag", ty := Ty.bool } ]
    returns :=
      [ { name := some "adjustedFirst", ty := Ty.uint 256 }
      , { name := some "count", ty := Ty.uint 256 }
      , { name := some "echo"
          ty := Ty.array (Ty.uint 256) none
          location := some DataLocation.memory } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.binary BinaryOp.add
                    (Expr.index (Expr.ident "items")
                      (Expr.literal (Literal.number "0")))
                    (Expr.ternary
                      (Expr.ident "flag")
                      (Expr.literal (Literal.number "1"))
                      (Expr.literal (Literal.number "0"))))
              , TupleItem.value
                  (Expr.member (Expr.ident "items") "length")
              , TupleItem.value (Expr.ident "items") ]))) }

def dynamicArrayAbiContract : ContractDecl :=
  { name := "DynamicArrayAbi"
    items := [ContractItem.function dynamicArrayAbiFunction] }

def dynamicArrayAbiValue : CoreValue :=
  SolidCore.Solidity.Source.Value.dynamicArray
    [ SolidCore.Solidity.Source.Value.word 10
    , SolidCore.Solidity.Source.Value.word 20
    , SolidCore.Solidity.Source.Value.word 30 ]

def dynamicArrayAbiCalldata : Option (List Byte) := do
  let contract ← ContractDecl.toCore? dynamicArrayAbiContract
  let function ← contract.findFunctionByName? "arrayInfo"
  SolidCore.Solidity.Source.ABI.calldataFor? function
    [ dynamicArrayAbiValue
    , SolidCore.Solidity.Source.Value.word 1 ]

def dynamicArrayAbiDecodedArgs : Option (List CoreValue) := do
  let calldata ← dynamicArrayAbiCalldata
  SolidCore.Solidity.Source.ABI.decodeArgs?
    [ SolidCore.Solidity.Source.Ty.dynamicArray
        SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.bool ]
    (calldata.drop SolidCore.Solidity.Source.ABI.selectorBytes)

def dynamicArrayAbiExpectedOutput : Option (List Byte) :=
  SolidCore.Solidity.Source.ABI.encodeValues?
    [ SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.dynamicArray
        SolidCore.Solidity.Source.Ty.uint256 ]
    [ SolidCore.Solidity.Source.Value.word 11
    , SolidCore.Solidity.Source.Value.word 3
    , dynamicArrayAbiValue ]

def dynamicArrayAbiCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? dynamicArrayAbiContract
  let calldata ← dynamicArrayAbiCalldata
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    32 contract SolidCore.Solidity.Source.State.empty calldata

def dynamicArrayAbiOutputMatchesExpected : Option Bool := do
  let result ← dynamicArrayAbiCalldataResult
  let expected ← dynamicArrayAbiExpectedOutput
  some (result.success && result.output == expected)

def dynamicBytesArrayAbiFunction : FunctionDecl :=
  { name := some "bytesArray"
    params :=
      [ { name := some "items"
          ty := Ty.array Ty.bytes none
          location := some DataLocation.calldata } ]
    returns :=
      [ { name := some "firstLength", ty := Ty.uint 256 }
      , { name := some "count", ty := Ty.uint 256 }
      , { name := some "echo"
          ty := Ty.array Ty.bytes none
          location := some DataLocation.memory } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.member
                    (Expr.index (Expr.ident "items")
                      (Expr.literal (Literal.number "0")))
                    "length")
              , TupleItem.value
                  (Expr.member (Expr.ident "items") "length")
              , TupleItem.value (Expr.ident "items") ]))) }

def dynamicBytesArrayAbiContract : ContractDecl :=
  { name := "DynamicBytesArrayAbi"
    items := [ContractItem.function dynamicBytesArrayAbiFunction] }

def dynamicBytesArrayAbiValue : CoreValue :=
  SolidCore.Solidity.Source.Value.dynamicArray
    [ SolidCore.Solidity.Source.Value.bytes [1, 2]
    , SolidCore.Solidity.Source.Value.bytes [3, 4, 5] ]

def dynamicBytesArrayAbiCalldata : Option (List Byte) := do
  let contract ← ContractDecl.toCore? dynamicBytesArrayAbiContract
  let function ← contract.findFunctionByName? "bytesArray"
  SolidCore.Solidity.Source.ABI.calldataFor? function
    [dynamicBytesArrayAbiValue]

def dynamicBytesArrayAbiDecodedArgs : Option (List CoreValue) := do
  let calldata ← dynamicBytesArrayAbiCalldata
  SolidCore.Solidity.Source.ABI.decodeArgs?
    [ SolidCore.Solidity.Source.Ty.dynamicArray
        SolidCore.Solidity.Source.Ty.bytesCalldata ]
    (calldata.drop SolidCore.Solidity.Source.ABI.selectorBytes)

def dynamicBytesArrayAbiExpectedOutput : Option (List Byte) :=
  SolidCore.Solidity.Source.ABI.encodeValues?
    [ SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.dynamicArray
        SolidCore.Solidity.Source.Ty.bytesCalldata ]
    [ SolidCore.Solidity.Source.Value.word 2
    , SolidCore.Solidity.Source.Value.word 2
    , dynamicBytesArrayAbiValue ]

def dynamicBytesArrayAbiCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? dynamicBytesArrayAbiContract
  let calldata ← dynamicBytesArrayAbiCalldata
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    32 contract SolidCore.Solidity.Source.State.empty calldata

def dynamicBytesArrayAbiOutputMatchesExpected : Option Bool := do
  let result ← dynamicBytesArrayAbiCalldataResult
  let expected ← dynamicBytesArrayAbiExpectedOutput
  some (result.success && result.output == expected)

def msgSigFunction : FunctionDecl :=
  { name := some "sig"
    returns := [{ name := some "out", ty := Ty.bytesN 4 }]
    body :=
      some
        (Stmt.returnValues
          (some (Expr.member (Expr.ident "msg") "sig"))) }

def msgSigContract : ContractDecl :=
  { name := "MsgSig"
    items := [ContractItem.function msgSigFunction] }

def msgSigCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? msgSigContract
  let function ← contract.findFunctionByName? "sig"
  let calldata ← SolidCore.Solidity.Source.ABI.calldataFor? function []
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    8 contract SolidCore.Solidity.Source.State.empty calldata

def fixedBytesEchoFunction : FunctionDecl :=
  { name := some "echo4"
    params := [{ name := some "value", ty := Ty.bytesN 4 }]
    returns := [{ name := some "out", ty := Ty.bytesN 4 }]
    body := some (Stmt.returnValues (some (Expr.ident "value"))) }

def fixedBytesEchoContract : ContractDecl :=
  { name := "FixedBytesEcho"
    items := [ContractItem.function fixedBytesEchoFunction] }

def fixedBytesEchoCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? fixedBytesEchoContract
  let function ← contract.findFunctionByName? "echo4"
  let calldata ←
    SolidCore.Solidity.Source.ABI.calldataFor? function
      [SolidCore.Solidity.Source.Value.word 0xaabbccdd]
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract SolidCore.Solidity.Source.State.empty calldata

def environmentGlobalsFunction : FunctionDecl :=
  { name := some "env"
    returns :=
      [ { name := some "timestamp", ty := Ty.uint 256 }
      , { name := some "number", ty := Ty.uint 256 }
      , { name := some "origin", ty := Ty.address false }
      , { name := some "gasprice", ty := Ty.uint 256 }
      , { name := some "remaining", ty := Ty.uint 256 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.member (Expr.ident "block") "timestamp")
              , TupleItem.value
                  (Expr.member (Expr.ident "block") "number")
              , TupleItem.value
                  (Expr.member (Expr.ident "tx") "origin")
              , TupleItem.value
                  (Expr.member (Expr.ident "tx") "gasprice")
              , TupleItem.value
                  (Expr.call (Expr.ident "gasleft") []) ]))) }

def environmentGlobalsContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    blockEnv :=
      { SolidCore.Solidity.Source.BlockEnv.empty with
        timestamp := 100
        number := 7 }
    txEnv :=
      { SolidCore.Solidity.Source.TxEnv.empty with
        origin := 0xabc
        gasprice := 50 }
    gasleft := 999 }

def environmentGlobalsCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] environmentGlobalsContext
    SolidCore.Solidity.Source.State.empty environmentGlobalsFunction []

def environmentHashFunction : FunctionDecl :=
  { name := some "hashes"
    returns :=
      [ { name := some "blockHash", ty := Ty.bytesN 32 }
      , { name := some "blobHash", ty := Ty.bytesN 32 }
      , { name := some "missingHash", ty := Ty.bytesN 32 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.call (Expr.ident "blockhash")
                    [Arg.positional (Expr.literal (Literal.number "7"))])
              , TupleItem.value
                  (Expr.call (Expr.ident "blobhash")
                    [Arg.positional (Expr.literal (Literal.number "1"))])
              , TupleItem.value
                  (Expr.call (Expr.ident "blockhash")
                    [Arg.positional (Expr.literal (Literal.number "8"))]) ]))) }

def environmentHashContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    blockEnv :=
      { SolidCore.Solidity.Source.BlockEnv.empty with
        number := 10
        blockHashes := [(7, 0x1234)] }
    txEnv :=
      { SolidCore.Solidity.Source.TxEnv.empty with
        blobHashes := [0, 0x5678] } }

def environmentHashCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] environmentHashContext
    SolidCore.Solidity.Source.State.empty environmentHashFunction []

def environmentHashMatches : Option Bool := do
  let result ← environmentHashCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word blockHash
      , SolidCore.Solidity.Source.Value.word blobHash
      , SolidCore.Solidity.Source.Value.word missingHash ] =>
      some
        (SolidCore.Solidity.Source.wordEq blockHash 0x1234 &&
          SolidCore.Solidity.Source.wordEq blobHash 0x5678 &&
          SolidCore.Solidity.Source.wordEq missingHash 0)
  | _ => some false

def environmentHashOutOfRangeContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    blockEnv :=
      { SolidCore.Solidity.Source.BlockEnv.empty with
        number := 300
        blockHashes := [(7, 0x1234), (8, 0x5678)] }
    txEnv :=
      { SolidCore.Solidity.Source.TxEnv.empty with
        blobHashes := [0x9999] } }

def environmentHashOutOfRangeCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] environmentHashOutOfRangeContext
    SolidCore.Solidity.Source.State.empty environmentHashFunction []

def environmentHashOutOfRangeMatches : Option Bool := do
  let result ← environmentHashOutOfRangeCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word blockHash
      , SolidCore.Solidity.Source.Value.word blobHash
      , SolidCore.Solidity.Source.Value.word missingHash ] =>
      some
        (SolidCore.Solidity.Source.wordEq blockHash 0 &&
          SolidCore.Solidity.Source.wordEq blobHash 0 &&
          SolidCore.Solidity.Source.wordEq missingHash 0)
  | _ => some false

def wordMaxLiteral : Literal :=
  Literal.number (toString (SolidCore.Solidity.Source.wordModulus - 1))

def modularArithmeticFunction : FunctionDecl :=
  { name := some "mods"
    returns :=
      [ { name := some "sumMod", ty := Ty.uint 256 }
      , { name := some "productMod", ty := Ty.uint 256 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.call (Expr.ident "addmod")
                    [ Arg.positional (Expr.literal wordMaxLiteral)
                    , Arg.positional (Expr.literal (Literal.number "2"))
                    , Arg.positional (Expr.literal (Literal.number "5")) ])
              , TupleItem.value
                  (Expr.call (Expr.ident "mulmod")
                    [ Arg.positional (Expr.literal wordMaxLiteral)
                    , Arg.positional (Expr.literal wordMaxLiteral)
                    , Arg.positional (Expr.literal (Literal.number "10")) ]) ]))) }

def modularArithmeticCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty modularArithmeticFunction []

def addmodZeroModulusStatement : Stmt :=
  Stmt.returnValues
    (some
      (Expr.call (Expr.ident "addmod")
        [ Arg.positional (Expr.literal (Literal.number "1"))
        , Arg.positional (Expr.literal (Literal.number "2"))
        , Arg.positional (Expr.literal (Literal.number "0")) ]))

def addmodZeroModulusResult : Option CoreResult :=
  Stmt.eval? 8 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState
      SolidCore.Solidity.Source.State.empty)
    addmodZeroModulusStatement

def keccakBuiltinFunction : FunctionDecl :=
  { name := some "hash"
    returns := [{ name := some "out", ty := Ty.bytesN 32 }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.ident "keccak256")
              [Arg.positional
                (Expr.literal (Literal.bytes [1, 2, 3]))]))) }

def keccakBuiltinCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty keccakBuiltinFunction []

def keccakBuiltinMatchesExpected : Option Bool := do
  let result ← keccakBuiltinCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value.asWord? with
      | some word =>
          some
            (word ==
              SolidCore.Solidity.Source.keccakWord [1, 2, 3])
      | none => none
  | _ => none

def erc7201BuiltinFunction : FunctionDecl :=
  { name := some "namespaceSlot"
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.ident "erc7201")
              [Arg.positional
                (Expr.literal (Literal.string "example.main"))]))) }

def erc7201BuiltinCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty erc7201BuiltinFunction []

def erc7201BuiltinMatchesEipExample : Option Bool := do
  let result ← erc7201BuiltinCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value.asWord? with
      | some slot =>
          some
            (slot ==
              0x183a6125c38840424c4a85fa12bab2ab606c4b6d0e7cc73c0c06ba5300eab500)
      | none => none
  | _ => none

def successfulPrecompileWordCall
    (kind : SharedSemantics.Precompile.Kind) (input : List Byte)
    (output : Word) : SolidCore.Solidity.Source.LowLevelCallResult :=
  { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
    target := SharedSemantics.Precompile.address kind
    calldata := input
    value := 0
    success := true
    output :=
      SolidCore.Solidity.Source.wordToBytesBE
        SolidCore.Solidity.Source.wordBytes output }

def externalCryptoHashFunction : FunctionDecl :=
  { name := some "externalHashes"
    returns :=
      [ { name := some "sha", ty := Ty.bytesN 32 }
      , { name := some "ripe", ty := Ty.bytesN 20 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.call (Expr.ident "sha256")
                    [Arg.positional
                      (Expr.literal (Literal.bytes [1, 2]))])
              , TupleItem.value
                  (Expr.call (Expr.ident "ripemd160")
                    [Arg.positional
                      (Expr.literal (Literal.bytes [3, 4]))]) ]))) }

def externalCryptoHashContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    lowLevelCallResults :=
      [ successfulPrecompileWordCall
          SharedSemantics.Precompile.Kind.sha256 [1, 2] 0xaaaa
      , successfulPrecompileWordCall
          SharedSemantics.Precompile.Kind.ripemd160 [3, 4] 0xbbbb ] }

def externalCryptoHashCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] externalCryptoHashContext
    SolidCore.Solidity.Source.State.empty externalCryptoHashFunction []

def externalCryptoHashMatches : Option Bool := do
  let result ← externalCryptoHashCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word sha
      , SolidCore.Solidity.Source.Value.word ripe ] =>
      some
        (SolidCore.Solidity.Source.wordEq sha 0xaaaa &&
          SolidCore.Solidity.Source.wordEq ripe 0xbbbb)
  | _ => some false

def externalCryptoHashMissingFunction : FunctionDecl :=
  { name := some "missingHash"
    returns := [{ name := some "out", ty := Ty.bytesN 32 }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.ident "sha256")
              [Arg.positional
                (Expr.literal (Literal.bytes [9]))]))) }

def externalCryptoHashMissingResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty externalCryptoHashMissingFunction []

def externalCryptoHashMissingMatches : Option Bool := do
  let result ← externalCryptoHashMissingResult
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      some (SolidCore.Solidity.Source.wordEq code 0)
  | _ => some false

def ecrecoverBuiltinFunction : FunctionDecl :=
  { name := some "recover"
    returns :=
      [ { name := some "recovered", ty := Ty.address false }
      , { name := some "missing", ty := Ty.address false } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.call (Expr.ident "ecrecover")
                    [ Arg.positional (Expr.literal (Literal.number "17"))
                    , Arg.positional (Expr.literal (Literal.number "27"))
                    , Arg.positional (Expr.literal (Literal.number "34"))
                    , Arg.positional (Expr.literal (Literal.number "51")) ])
              , TupleItem.value
                  (Expr.call (Expr.ident "ecrecover")
                    [ Arg.positional (Expr.literal (Literal.number "68"))
                    , Arg.positional (Expr.literal (Literal.number "27"))
                    , Arg.positional (Expr.literal (Literal.number "34"))
                    , Arg.positional (Expr.literal (Literal.number "51")) ]) ]))) }

def ecrecoverBuiltinContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    lowLevelCallResults :=
      [ successfulPrecompileWordCall
          SharedSemantics.Precompile.Kind.ecrecover
          (SharedSemantics.Precompile.ecrecoverInput 17 27 34 51)
          0xcafe ] }

def ecrecoverBuiltinCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] ecrecoverBuiltinContext
    SolidCore.Solidity.Source.State.empty ecrecoverBuiltinFunction []

def ecrecoverBuiltinMatches : Option Bool := do
  let result ← ecrecoverBuiltinCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word recovered
      , SolidCore.Solidity.Source.Value.word missing ] =>
      some
        (SolidCore.Solidity.Source.wordEq recovered 0xcafe &&
          SolidCore.Solidity.Source.wordEq missing 0)
  | _ => some false

def abiEncodeCoreExprStatement : SolidCore.Solidity.Source.Stmt :=
  SolidCore.Solidity.Source.Stmt.returnValues
    [ SolidCore.Solidity.Source.Expr.abiEncode
        [ SolidCore.Solidity.Source.Ty.uint256
        , SolidCore.Solidity.Source.Ty.bytesCalldata ]
        [ SolidCore.Solidity.Source.Expr.word 7
        , SolidCore.Solidity.Source.Expr.byteArray [8, 9] ] ]

def abiEncodeCoreExprResult : Option CoreResult :=
  SolidCore.Solidity.Source.Stmt.eval 8
    SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState
      SolidCore.Solidity.Source.State.empty)
    abiEncodeCoreExprStatement

def abiEncodeCoreExprMatchesExpected : Option Bool := do
  let result ← abiEncodeCoreExprResult
  let expected ←
    SolidCore.Solidity.Source.abiEncodeValues?
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.bytesCalldata ]
      [ SolidCore.Solidity.Source.Value.word 7
      , SolidCore.Solidity.Source.Value.bytes [8, 9] ]
  match result with
  | SolidCore.Solidity.Source.Result.returned _ [value] =>
      match value.asBytes? with
      | some bytes => some (bytes == expected)
      | none => none
  | _ => none

def abiEncodeSourceFunction : FunctionDecl :=
  { name := some "pack"
    params :=
      [ { name := some "x", ty := Ty.uint 256 }
      , { name := some "payload", ty := Ty.bytes
          location := some DataLocation.calldata } ]
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.member (Expr.ident "abi") "encode")
              [ Arg.positional
                  (Expr.call (Expr.typeName (Ty.uint 256))
                    [Arg.positional (Expr.ident "x")])
              , Arg.positional
                  (Expr.call (Expr.typeName Ty.bytes)
                    [Arg.positional (Expr.ident "payload")]) ]))) }

def abiEncodeSourceCallResult : Option CoreCallResult :=
  FunctionDecl.call? 12 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty abiEncodeSourceFunction
    [ SolidCore.Solidity.Source.Value.word 7
    , SolidCore.Solidity.Source.Value.bytes [8, 9] ]

def abiEncodeSourceMatchesExpected : Option Bool := do
  let result ← abiEncodeSourceCallResult
  let expected ←
    SolidCore.Solidity.Source.abiEncodeValues?
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.bytesCalldata ]
      [ SolidCore.Solidity.Source.Value.word 7
      , SolidCore.Solidity.Source.Value.bytes [8, 9] ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value.asBytes? with
      | some bytes => some (bytes == expected)
      | none => none
  | _ => none

def abiEncodeInferredSourceFunction : FunctionDecl :=
  { name := some "packInferred"
    params :=
      [ { name := some "x", ty := Ty.uint 256 }
      , { name := some "payload", ty := Ty.bytes
          location := some DataLocation.calldata } ]
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.member (Expr.ident "abi") "encode")
              [ Arg.positional (Expr.ident "x")
              , Arg.positional (Expr.ident "payload") ]))) }

def abiEncodeInferredSourceCallResult : Option CoreCallResult :=
  FunctionDecl.call? 12 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty abiEncodeInferredSourceFunction
    [ SolidCore.Solidity.Source.Value.word 7
    , SolidCore.Solidity.Source.Value.bytes [8, 9] ]

def abiEncodeInferredSourceMatchesExpected : Option Bool := do
  let result ← abiEncodeInferredSourceCallResult
  let expected ←
    SolidCore.Solidity.Source.abiEncodeValues?
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.bytesCalldata ]
      [ SolidCore.Solidity.Source.Value.word 7
      , SolidCore.Solidity.Source.Value.bytes [8, 9] ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value.asBytes? with
      | some bytes => some (bytes == expected)
      | none => none
  | _ => none

def abiEncodeLocalInferredSourceFunction : FunctionDecl :=
  { name := some "packLocal"
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [{ name := some "y", ty := some (Ty.uint 256) }]
              (some (Expr.literal (Literal.number "7")))
          , Stmt.returnValues
              (some
                (Expr.call (Expr.member (Expr.ident "abi") "encode")
                  [Arg.positional (Expr.ident "y")])) ]) }

def abiEncodeLocalInferredSourceCallResult : Option CoreCallResult :=
  FunctionDecl.call? 12 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    abiEncodeLocalInferredSourceFunction []

def abiEncodeLocalInferredSourceMatchesExpected : Option Bool := do
  let result ← abiEncodeLocalInferredSourceCallResult
  let expected ←
    SolidCore.Solidity.Source.abiEncodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value.asBytes? with
      | some bytes => some (bytes == expected)
      | none => none
  | _ => none

def keccakAbiEncodeSourceFunction : FunctionDecl :=
  { name := some "hashPack"
    returns := [{ name := some "out", ty := Ty.bytesN 32 }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.ident "keccak256")
              [Arg.positional
                (Expr.call (Expr.member (Expr.ident "abi") "encode")
                  [ Arg.positional
                      (Expr.call (Expr.typeName (Ty.uint 256))
                        [Arg.positional
                          (Expr.literal (Literal.number "7"))])
                  , Arg.positional
                      (Expr.call (Expr.typeName Ty.bytes)
                        [Arg.positional
                          (Expr.literal (Literal.bytes [8, 9]))]) ])]))) }

def keccakAbiEncodeSourceCallResult : Option CoreCallResult :=
  FunctionDecl.call? 12 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty keccakAbiEncodeSourceFunction []

def keccakAbiEncodeSourceMatchesExpected : Option Bool := do
  let result ← keccakAbiEncodeSourceCallResult
  let encoded ←
    SolidCore.Solidity.Source.abiEncodeValues?
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.bytesCalldata ]
      [ SolidCore.Solidity.Source.Value.word 7
      , SolidCore.Solidity.Source.Value.bytes [8, 9] ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value.asWord? with
      | some word =>
          some
            (word ==
              SolidCore.Solidity.Source.keccakWord encoded)
      | none => none
  | _ => none

def selectorEncodingSignature : String :=
  "set(uint256)"

def selectorEncodingSelector : Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature
    selectorEncodingSignature

def abiEncodeWithSelectorSourceFunction : FunctionDecl :=
  { name := some "callData"
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call
              (Expr.member (Expr.ident "abi") "encodeWithSelector")
              [ Arg.positional
                  (Expr.call (Expr.typeName (Ty.bytesN 4))
                    [Arg.positional
                      (Expr.literal
                        (Literal.number
                          (toString selectorEncodingSelector)))])
              , Arg.positional
                  (Expr.call (Expr.typeName (Ty.uint 256))
                    [Arg.positional
                      (Expr.literal (Literal.number "7"))]) ]))) }

def abiEncodeWithSelectorSourceCallResult : Option CoreCallResult :=
  FunctionDecl.call? 12 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    abiEncodeWithSelectorSourceFunction []

def abiEncodeWithSelectorExpected : Option (List Byte) := do
  let encodedArgs ←
    SolidCore.Solidity.Source.abiEncodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  some
    (SolidCore.Solidity.Source.wordToBytesBE
      SolidCore.Solidity.Source.selectorBytes
      selectorEncodingSelector ++ encodedArgs)

def abiEncodeWithSelectorSourceMatchesExpected : Option Bool := do
  let result ← abiEncodeWithSelectorSourceCallResult
  let expected ← abiEncodeWithSelectorExpected
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value.asBytes? with
      | some bytes => some (bytes == expected)
      | none => none
  | _ => none

def abiEncodeWithSignatureSourceFunction : FunctionDecl :=
  { name := some "callDataBySignature"
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call
              (Expr.member (Expr.ident "abi") "encodeWithSignature")
              [ Arg.positional
                  (Expr.literal
                    (Literal.string selectorEncodingSignature))
              , Arg.positional
                  (Expr.call (Expr.typeName (Ty.uint 256))
                    [Arg.positional
                      (Expr.literal (Literal.number "7"))]) ]))) }

def abiEncodeWithSignatureSourceCallResult : Option CoreCallResult :=
  FunctionDecl.call? 12 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    abiEncodeWithSignatureSourceFunction []

def abiEncodeWithSignatureSourceMatchesExpected : Option Bool := do
  let result ← abiEncodeWithSignatureSourceCallResult
  let expected ← abiEncodeWithSelectorExpected
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value.asBytes? with
      | some bytes => some (bytes == expected)
      | none => none
  | _ => none

def abiEncodeWithRuntimeSignatureSourceFunction : FunctionDecl :=
  { name := some "callDataByRuntimeSignature"
    params :=
      [ { name := some "signature"
          ty := Ty.string
          location := some DataLocation.calldata }
      , { name := some "value", ty := Ty.uint 256 } ]
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call
              (Expr.member (Expr.ident "abi") "encodeWithSignature")
              [ Arg.positional (Expr.ident "signature")
              , Arg.positional (Expr.ident "value") ]))) }

def abiEncodeWithRuntimeSignatureSourceCallResult : Option CoreCallResult :=
  FunctionDecl.call? 12 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    abiEncodeWithRuntimeSignatureSourceFunction
    [ SolidCore.Solidity.Source.Value.bytes
        (stringUtf8Bytes selectorEncodingSignature)
    , SolidCore.Solidity.Source.Value.word 7 ]

def abiEncodeWithRuntimeSignatureSourceMatchesExpected : Option Bool := do
  let result ← abiEncodeWithRuntimeSignatureSourceCallResult
  let expected ← abiEncodeWithSelectorExpected
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value.asBytes? with
      | some bytes => some (bytes == expected)
      | none => none
  | _ => none

def abiEncodeCallSignature : String :=
  "set(uint256,bytes)"

def abiEncodeCallSelector : Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature
    abiEncodeCallSignature

def abiEncodeCallSourceFunction : FunctionDecl :=
  { name := some "callDataByEncodeCall"
    params :=
      [ { name := some "target"
          ty := Ty.user { segments := ["Target"] } }
      , { name := some "x", ty := Ty.uint 256 }
      , { name := some "payload", ty := Ty.bytes
          location := some DataLocation.calldata } ]
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call
              (Expr.member (Expr.ident "abi") "encodeCall")
              [ Arg.positional
                  (Expr.member (Expr.ident "target") "set")
              , Arg.positional
                  (Expr.tuple
                    [ TupleItem.value (Expr.ident "x")
                    , TupleItem.value (Expr.ident "payload") ]) ]))) }

def abiEncodeCallSourceCallResult : Option CoreCallResult :=
  FunctionDecl.call? 12 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    abiEncodeCallSourceFunction
    [ SolidCore.Solidity.Source.Value.word 0x100
    , SolidCore.Solidity.Source.Value.word 7
    , SolidCore.Solidity.Source.Value.bytes [8, 9] ]

def abiEncodeCallExpected : Option (List Byte) := do
  let encodedArgs ←
    SolidCore.Solidity.Source.abiEncodeValues?
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.bytesCalldata ]
      [ SolidCore.Solidity.Source.Value.word 7
      , SolidCore.Solidity.Source.Value.bytes [8, 9] ]
  some
    (SolidCore.Solidity.Source.wordToBytesBE
      SolidCore.Solidity.Source.selectorBytes
      abiEncodeCallSelector ++ encodedArgs)

def abiEncodeCallSourceMatchesExpected : Option Bool := do
  let result ← abiEncodeCallSourceCallResult
  let expected ← abiEncodeCallExpected
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value.asBytes? with
      | some bytes => some (bytes == expected)
      | none => none
  | _ => none

def abiEncodePackedSourceFunction : FunctionDecl :=
  { name := some "packed"
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call
              (Expr.member (Expr.ident "abi") "encodePacked")
              [ Arg.positional
                  (Expr.call (Expr.typeName (Ty.bytesN 1))
                    [Arg.positional
                      (Expr.literal (Literal.number "66"))])
              , Arg.positional
                  (Expr.call (Expr.typeName (Ty.uint 256))
                    [Arg.positional
                      (Expr.literal (Literal.number "3"))])
              , Arg.positional
                  (Expr.call (Expr.typeName Ty.bytes)
                    [Arg.positional
                      (Expr.literal (Literal.string "Hi"))]) ]))) }

def abiEncodePackedSourceCallResult : Option CoreCallResult :=
  FunctionDecl.call? 12 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    abiEncodePackedSourceFunction []

def abiEncodePackedSourceMatchesExpected : Option Bool := do
  let result ← abiEncodePackedSourceCallResult
  let expected ←
    SolidCore.Solidity.Source.abiEncodePackedValues?
      [ SolidCore.Solidity.Source.Ty.fixedBytes 1
      , SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.bytesCalldata ]
      [ SolidCore.Solidity.Source.Value.word 66
      , SolidCore.Solidity.Source.Value.word 3
      , SolidCore.Solidity.Source.Value.bytes [72, 105] ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value.asBytes? with
      | some bytes => some (bytes == expected)
      | none => none
  | _ => none

def abiEncodePackedInferredSourceFunction : FunctionDecl :=
  { name := some "packedInferred"
    params :=
      [ { name := some "tag", ty := Ty.bytesN 1 }
      , { name := some "x", ty := Ty.uint 256 }
      , { name := some "payload", ty := Ty.bytes
          location := some DataLocation.calldata } ]
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call
              (Expr.member (Expr.ident "abi") "encodePacked")
              [ Arg.positional (Expr.ident "tag")
              , Arg.positional (Expr.ident "x")
              , Arg.positional (Expr.ident "payload") ]))) }

def abiEncodePackedInferredSourceCallResult : Option CoreCallResult :=
  FunctionDecl.call? 12 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    abiEncodePackedInferredSourceFunction
    [ SolidCore.Solidity.Source.Value.word 66
    , SolidCore.Solidity.Source.Value.word 3
    , SolidCore.Solidity.Source.Value.bytes [72, 105] ]

def abiEncodePackedInferredSourceMatchesExpected : Option Bool := do
  let result ← abiEncodePackedInferredSourceCallResult
  let expected ←
    SolidCore.Solidity.Source.abiEncodePackedValues?
      [ SolidCore.Solidity.Source.Ty.fixedBytes 1
      , SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.bytesCalldata ]
      [ SolidCore.Solidity.Source.Value.word 66
      , SolidCore.Solidity.Source.Value.word 3
      , SolidCore.Solidity.Source.Value.bytes [72, 105] ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] =>
      match value.asBytes? with
      | some bytes => some (bytes == expected)
      | none => none
  | _ => none

def abiDecodeExampleBytes : Option (List Byte) :=
  SolidCore.Solidity.Source.abiEncodeValues?
    [ SolidCore.Solidity.Source.Ty.uint256
    , SolidCore.Solidity.Source.Ty.bytesCalldata ]
    [ SolidCore.Solidity.Source.Value.word 7
    , SolidCore.Solidity.Source.Value.bytes [8, 9] ]

def abiDecodeSingleSourceFunction : FunctionDecl :=
  { name := some "decodeOne"
    params :=
      [{ name := some "data", ty := Ty.bytes
         location := some DataLocation.calldata }]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.member (Expr.ident "abi") "decode")
              [ Arg.positional (Expr.ident "data")
              , Arg.positional (Expr.typeName (Ty.uint 256)) ]))) }

def abiDecodeSingleSourceCallResult : Option CoreCallResult := do
  let encoded ←
    SolidCore.Solidity.Source.abiEncodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  FunctionDecl.call? 12 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    abiDecodeSingleSourceFunction
    [SolidCore.Solidity.Source.Value.bytes encoded]

def abiDecodeSingleSourceMatchesExpected : Option Bool := do
  let result ← abiDecodeSingleSourceCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 7)
  | _ => none

def abiDecodeMultiSourceFunction : FunctionDecl :=
  { name := some "decodePair"
    params :=
      [{ name := some "data", ty := Ty.bytes
         location := some DataLocation.calldata }]
    returns :=
      [ { name := some "x", ty := Ty.uint 256 }
      , { name := some "payload", ty := Ty.bytes } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.member (Expr.ident "abi") "decode")
              [ Arg.positional (Expr.ident "data")
              , Arg.positional
                  (Expr.tuple
                    [ TupleItem.value (Expr.typeName (Ty.uint 256))
                    , TupleItem.value (Expr.typeName Ty.bytes) ]) ]))) }

def abiDecodeMultiSourceCallResult : Option CoreCallResult := do
  let encoded ← abiDecodeExampleBytes
  FunctionDecl.call? 16 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    abiDecodeMultiSourceFunction
    [SolidCore.Solidity.Source.Value.bytes encoded]

def abiDecodeMultiSourceMatchesExpected : Option Bool := do
  let result ← abiDecodeMultiSourceCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word value
      , SolidCore.Solidity.Source.Value.bytes payload ] =>
      some (value == 7 && payload == [8, 9])
  | _ => none

def abiDecodeMalformedSourceFunction : FunctionDecl :=
  { name := some "badDecode"
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.member (Expr.ident "abi") "decode")
              [ Arg.positional (Expr.literal (Literal.bytes [1, 2, 3]))
              , Arg.positional (Expr.typeName (Ty.uint 256)) ]))) }

def abiDecodeMalformedSourceCallResult : Option CoreCallResult :=
  FunctionDecl.call? 12 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    abiDecodeMalformedSourceFunction []

def abiDecodeMalformedSourceReverts : Option Bool := do
  let result ← abiDecodeMalformedSourceCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      some (code == 0)
  | _ => some false

def uintTypeInfoFunction : FunctionDecl :=
  { name := some "limits"
    returns :=
      [ { name := some "min256", ty := Ty.uint 256 }
      , { name := some "max8", ty := Ty.uint 256 }
      , { name := some "max256", ty := Ty.uint 256 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.member (Expr.typeName (Ty.uint 256)) "min")
              , TupleItem.value
                  (Expr.member (Expr.typeName (Ty.uint 8)) "max")
              , TupleItem.value
                  (Expr.member (Expr.typeName (Ty.uint 0)) "max") ]))) }

def uintTypeInfoCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty uintTypeInfoFunction []

def contractTypeNameInfoFunction : FunctionDecl :=
  { name := some "contractName"
    returns := [{ name := some "out", ty := Ty.string }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.member
              (Expr.typeName (Ty.user { segments := ["Vault"] }))
              "name"))) }

def contractTypeNameInfoMatches : Option Bool := do
  let result ←
    FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty contractTypeNameInfoFunction []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      some (bytes == "Vault".toList.map Char.toNat)
  | _ => some false

def contractTypeCodeInfoContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    contractCreationCodes := [("Target", [1, 2, 3, 4])]
    contractRuntimeCodes := [("Target", [5, 6, 7])] }

def targetContractType : Ty :=
  Ty.user { segments := ["Target"] }

def targetContractCreationCode : Expr :=
  Expr.member (Expr.typeName targetContractType) "creationCode"

def targetContractRuntimeCode : Expr :=
  Expr.member (Expr.typeName targetContractType) "runtimeCode"

def contractTypeCodeInfoFunction : FunctionDecl :=
  { name := some "codeInfo"
    returns :=
      [ { name := some "creationLen", ty := Ty.uint 256 }
      , { name := some "runtimeLen", ty := Ty.uint 256 }
      , { name := some "runtimeBytes", ty := Ty.bytes } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.member targetContractCreationCode "length")
              , TupleItem.value
                  (Expr.member targetContractRuntimeCode "length")
              , TupleItem.value targetContractRuntimeCode ]))) }

def contractTypeCodeInfoMatches : Option Bool := do
  let result ←
    FunctionDecl.call? 8 [] [] contractTypeCodeInfoContext
      SolidCore.Solidity.Source.State.empty contractTypeCodeInfoFunction []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word creationLen
      , SolidCore.Solidity.Source.Value.word runtimeLen
      , SolidCore.Solidity.Source.Value.bytes runtimeBytes ] =>
      some
        (creationLen == 4 && runtimeLen == 3 &&
          runtimeBytes == [5, 6, 7])
  | _ => some false

def contractTypeRuntimeCodeAbiFunction : FunctionDecl :=
  { name := some "runtimeCodeAbi"
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.member (Expr.ident "abi") "encode")
              [Arg.positional targetContractRuntimeCode]))) }

def contractTypeRuntimeCodeAbiExpected : Option (List Byte) :=
  SolidCore.Solidity.Source.ABI.encodeValues?
    [SolidCore.Solidity.Source.Ty.bytesCalldata]
    [SolidCore.Solidity.Source.Value.bytes [5, 6, 7]]

def contractTypeRuntimeCodeAbiMatches : Option Bool := do
  let result ←
    FunctionDecl.call? 8 [] [] contractTypeCodeInfoContext
      SolidCore.Solidity.Source.State.empty
      contractTypeRuntimeCodeAbiFunction []
  let expected ← contractTypeRuntimeCodeAbiExpected
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      some (bytes == expected)
  | _ => some false

def interfaceIdBaseInterface : ContractDecl :=
  { name := "IBase"
    kind := ContractKind.interface
    items :=
      [ ContractItem.function
          { name := some "supportsInterface"
            visibility := some Visibility.external_
            params := [{ name := some "id", ty := Ty.bytesN 4 }]
            returns := [{ name := some "ok", ty := Ty.bool }]
            body := none } ] }

def interfaceIdTokenInterface : ContractDecl :=
  { name := "IToken"
    kind := ContractKind.interface
    bases := [{ base := { segments := ["IBase"] } }]
    items :=
      [ ContractItem.function
          { name := some "balanceOf"
            visibility := some Visibility.external_
            params := [{ name := some "owner", ty := Ty.address false }]
            returns := [{ name := some "balance", ty := Ty.uint 256 }]
            body := none }
      , ContractItem.function
          { name := some "transfer"
            visibility := some Visibility.external_
            params :=
              [ { name := some "to", ty := Ty.address false }
              , { name := some "amount", ty := Ty.uint 256 } ]
            returns := [{ name := some "ok", ty := Ty.bool }]
            body := none } ] }

def interfaceIdReaderContract : ContractDecl :=
  { name := "InterfaceInfo"
    items :=
      [ ContractItem.function
          { name := some "tokenInterfaceId"
            returns := [{ name := some "out", ty := Ty.bytesN 4 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.member
                      (Expr.typeName (Ty.user { segments := ["IToken"] }))
                      "interfaceId"))) } ] }

def interfaceIdSourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.contract interfaceIdBaseInterface
      , SourceItem.contract interfaceIdTokenInterface
      , SourceItem.contract interfaceIdReaderContract ] }

def interfaceIdTokenExpected : Word :=
  SharedSemantics.xorWord
    (SolidCore.Solidity.Source.ABI.selectorFromSignature
      "balanceOf(address)")
    (SolidCore.Solidity.Source.ABI.selectorFromSignature
      "transfer(address,uint256)")

def interfaceIdTokenIncludingInherited : Word :=
  SharedSemantics.xorWord
    interfaceIdTokenExpected
    (SolidCore.Solidity.Source.ABI.selectorFromSignature
      "supportsInterface(bytes4)")

def interfaceIdExcludesInheritedMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 interfaceIdSourceUnit "InterfaceInfo"
      (SolidCore.Solidity.Source.CallTarget.name "tokenInterfaceId")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word interfaceId] =>
      some
        (interfaceId == interfaceIdTokenExpected &&
          interfaceId != interfaceIdTokenIncludingInherited)
  | _ => some false

def selectorInfoContract : ContractDecl :=
  { name := "SelectorInfo"
    items :=
      [ ContractItem.stateVar
          { name := "stored"
            ty := Ty.uint 256
            visibility := some Visibility.public_ }
      , ContractItem.errorDecl
          { name := "Bad"
            params := [{ name := some "value", ty := Ty.uint 256 }] }
      , ContractItem.function
          { name := some "set"
            visibility := some Visibility.external_
            params := [{ name := some "value", ty := Ty.uint 256 }]
            body := some Stmt.empty }
      , ContractItem.function
          { name := some "selectors"
            params :=
              [ { name := some "target"
                  ty := Ty.user { segments := ["SelectorInfo"] } } ]
            returns :=
              [ { name := some "setSelector", ty := Ty.bytesN 4 }
              , { name := some "badSelector", ty := Ty.bytesN 4 }
              , { name := some "getterSelector", ty := Ty.bytesN 4 }
              , { name := some "setAddress", ty := Ty.address false }
              , { name := some "targetSetAddress", ty := Ty.address false } ]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.tuple
                      [ TupleItem.value
                          (Expr.member
                            (Expr.member (Expr.ident "this") "set")
                            "selector")
                      , TupleItem.value
                          (Expr.member (Expr.ident "Bad") "selector")
                      , TupleItem.value
                          (Expr.member
                            (Expr.member (Expr.ident "this") "stored")
                            "selector")
                      , TupleItem.value
                          (Expr.member
                            (Expr.member (Expr.ident "this") "set")
                            "address")
                      , TupleItem.value
                          (Expr.member
                            (Expr.member (Expr.ident "target") "set")
                            "address") ]))) } ] }

def selectorInfoMatches : Option Bool := do
  let result ←
    ContractDecl.call? 32 selectorInfoContract
      (SolidCore.Solidity.Source.CallTarget.name "selectors")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word setSelector
      , SolidCore.Solidity.Source.Value.word badSelector
      , SolidCore.Solidity.Source.Value.word getterSelector
      , SolidCore.Solidity.Source.Value.word setAddress
      , SolidCore.Solidity.Source.Value.word targetSetAddress ] =>
      some
        (setSelector ==
            SolidCore.Solidity.Source.ABI.selectorFromSignature
              "set(uint256)" &&
          badSelector ==
            SolidCore.Solidity.Source.ABI.selectorFromSignature
              "Bad(uint256)" &&
          getterSelector ==
            SolidCore.Solidity.Source.ABI.selectorFromSignature
              "stored()" &&
          setAddress == 0 &&
          targetSetAddress == 0xbeef)
  | _ => some false

def overloadedSelectorRejectedContract : ContractDecl :=
  { name := "OverloadedSelector"
    items :=
      [ ContractItem.function
          { name := some "pick"
            params := [{ name := some "value", ty := Ty.uint 256 }]
            body := some Stmt.empty }
      , ContractItem.function
          { name := some "pick"
            params := [{ name := some "payload", ty := Ty.bytes }]
            body := some Stmt.empty }
      , ContractItem.function
          { name := some "selector"
            returns := [{ name := some "out", ty := Ty.bytesN 4 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.member
                      (Expr.member (Expr.ident "this") "pick")
                      "selector"))) } ] }

def overloadedSelectorRejected : Bool :=
  match ContractDecl.toCore? overloadedSelectorRejectedContract with
  | none => true
  | some _ => false

def signedIntArithmeticFunction : FunctionDecl :=
  { name := some "signedOps"
    params :=
      [ { name := some "a", ty := Ty.int 256 }
      , { name := some "b", ty := Ty.int 256 } ]
    returns :=
      [ { name := some "quotient", ty := Ty.int 256 }
      , { name := some "remainder", ty := Ty.int 256 }
      , { name := some "less", ty := Ty.bool } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.binary BinaryOp.div
                    (Expr.ident "a") (Expr.ident "b"))
              , TupleItem.value
                  (Expr.binary BinaryOp.mod
                    (Expr.ident "a") (Expr.ident "b"))
              , TupleItem.value
                  (Expr.binary BinaryOp.lt
                    (Expr.ident "a") (Expr.ident "b")) ]))) }

def signedIntArithmeticCallResult : Option CoreCallResult :=
  FunctionDecl.call? 16 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty signedIntArithmeticFunction
    [ SolidCore.Solidity.Source.Value.int
        (SharedSemantics.signedToWord (-5))
    , SolidCore.Solidity.Source.Value.int 2 ]

def signedSarFunction : FunctionDecl :=
  { name := some "signedSar"
    params :=
      [ { name := some "value", ty := Ty.int 256 }
      , { name := some "shift", ty := Ty.uint 256 } ]
    returns := [{ name := some "out", ty := Ty.int 256 }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.binary BinaryOp.sar
              (Expr.ident "value")
              (Expr.ident "shift")))) }

def signedSarMatches : Option Bool := do
  let result ←
    FunctionDecl.call? 16 [] [] SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty signedSarFunction
      [ SolidCore.Solidity.Source.Value.int
          (SharedSemantics.signedToWord (-5))
      , SolidCore.Solidity.Source.Value.word 1 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.int value] =>
      some
        (SolidCore.Solidity.Source.wordEq value
          (SharedSemantics.signedToWord (-3)))
  | _ => some false

def signedSarAssignFunction : FunctionDecl :=
  { name := some "signedSarAssign"
    params :=
      [ { name := some "value", ty := Ty.int 256 }
      , { name := some "shift", ty := Ty.uint 256 } ]
    returns := [{ name := some "out", ty := Ty.int 256 }]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [{ name := some "x", ty := some (Ty.int 256) }]
              (some (Expr.ident "value"))
          , Stmt.expr
              (Expr.assign (Expr.ident "x") AssignOp.sarAssign
                (Expr.ident "shift"))
          , Stmt.returnValues (some (Expr.ident "x")) ]) }

def signedSarAssignMatches : Option Bool := do
  let result ←
    FunctionDecl.call? 16 [] [] SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty signedSarAssignFunction
      [ SolidCore.Solidity.Source.Value.int
          (SharedSemantics.signedToWord (-5))
      , SolidCore.Solidity.Source.Value.word 1 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.int value] =>
      some
        (SolidCore.Solidity.Source.wordEq value
          (SharedSemantics.signedToWord (-3)))
  | _ => some false

def signedIntAbiContract : ContractDecl :=
  { name := "SignedAbi"
    items := [ContractItem.function signedIntArithmeticFunction] }

def signedIntAbiCalldata : Option (List Byte) := do
  let contract ← ContractDecl.toCore? signedIntAbiContract
  let function ← contract.findFunctionByName? "signedOps"
  SolidCore.Solidity.Source.ABI.calldataFor? function
    [ SolidCore.Solidity.Source.Value.int
        (SharedSemantics.signedToWord (-5))
    , SolidCore.Solidity.Source.Value.int 2 ]

def signedIntAbiExpectedOutput : Option (List Byte) :=
  SolidCore.Solidity.Source.ABI.encodeValues?
    [ SolidCore.Solidity.Source.Ty.int256
    , SolidCore.Solidity.Source.Ty.int256
    , SolidCore.Solidity.Source.Ty.bool ]
    [ SolidCore.Solidity.Source.Value.int
        (SharedSemantics.signedToWord (-2))
    , SolidCore.Solidity.Source.Value.int
        (SharedSemantics.signedToWord (-1))
    , SolidCore.Solidity.Source.Value.word 1 ]

def signedIntAbiCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? signedIntAbiContract
  let calldata ← signedIntAbiCalldata
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    24 contract SolidCore.Solidity.Source.State.empty calldata

def signedIntAbiOutputMatchesExpected : Option Bool := do
  let result ← signedIntAbiCalldataResult
  let expected ← signedIntAbiExpectedOutput
  some (result.success && result.output == expected)

def intTypeInfoFunction : FunctionDecl :=
  { name := some "signedLimits"
    returns :=
      [ { name := some "min256", ty := Ty.int 256 }
      , { name := some "max256", ty := Ty.int 256 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.member (Expr.typeName (Ty.int 256)) "min")
              , TupleItem.value
                  (Expr.member (Expr.typeName (Ty.int 256)) "max") ]))) }

def intTypeInfoCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty intTypeInfoFunction []

def signedNegOverflowStatement : Stmt :=
  Stmt.returnValues
    (some
      (Expr.unary UnaryOp.neg
        (Expr.member (Expr.typeName (Ty.int 256)) "min")))

def signedNegOverflowResult : Option CoreResult :=
  Stmt.eval? 8 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState
      SolidCore.Solidity.Source.State.empty)
    signedNegOverflowStatement

def uncheckedSignedNegWrapStatement : Stmt :=
  Stmt.unchecked
    (Stmt.returnValues
      (some
        (Expr.unary UnaryOp.neg
          (Expr.member (Expr.typeName (Ty.int 256)) "min"))))

def uncheckedSignedNegWrapResult : Option CoreResult :=
  Stmt.eval? 8 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState
      SolidCore.Solidity.Source.State.empty)
    uncheckedSignedNegWrapStatement

def exponentiationStatement : Stmt :=
  Stmt.returnValues
    (some
      (Expr.binary BinaryOp.exp
        (Expr.literal (Literal.number "2"))
        (Expr.literal (Literal.number "8"))))

def exponentiationResult : Option CoreResult :=
  Stmt.eval? 8 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState
      SolidCore.Solidity.Source.State.empty)
    exponentiationStatement

def expOverflowBaseLiteral : Literal :=
  Literal.number (toString (2 ^ 128))

def exponentOverflowStatement : Stmt :=
  Stmt.returnValues
    (some
      (Expr.binary BinaryOp.exp
        (Expr.literal expOverflowBaseLiteral)
        (Expr.literal (Literal.number "2"))))

def exponentOverflowResult : Option CoreResult :=
  Stmt.eval? 8 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState
      SolidCore.Solidity.Source.State.empty)
    exponentOverflowStatement

def uncheckedExponentWrapStatement : Stmt :=
  Stmt.block
    [ Stmt.varDecl
        [{ name := some "x", ty := some (Ty.uint 256) }]
        none
    , Stmt.unchecked
        (Stmt.expr
          (Expr.assign (Expr.ident "x") AssignOp.assign
            (Expr.binary BinaryOp.exp
              (Expr.literal expOverflowBaseLiteral)
              (Expr.literal (Literal.number "2")))))
    , Stmt.returnValues (some (Expr.ident "x")) ]

def uncheckedExponentWrapResult : Option CoreResult :=
  Stmt.eval? 16 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState
      SolidCore.Solidity.Source.State.empty)
    uncheckedExponentWrapStatement

def requireCustomErrorContract : ContractDecl :=
  { name := "RequireCustom"
    items :=
      [ ContractItem.errorDecl
          { name := "TooSmall"
            params := [{ name := some "actual", ty := Ty.uint 256 }] }
      , ContractItem.function
          { name := some "check"
            params := [{ name := some "value", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.expr
                  (Expr.call (Expr.ident "require")
                    [ Arg.positional
                        (Expr.binary BinaryOp.gt
                          (Expr.ident "value")
                          (Expr.literal (Literal.number "10")))
                    , Arg.positional
                        (Expr.call (Expr.ident "TooSmall")
                          [Arg.positional (Expr.ident "value")]) ])) } ] }

def requireCustomErrorAbiResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? requireCustomErrorContract
  let function ← contract.findFunctionByName? "check"
  let calldata ←
    SolidCore.Solidity.Source.ABI.calldataFor? function
      [SolidCore.Solidity.Source.Value.word 4]
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract SolidCore.Solidity.Source.State.empty calldata

def requireCustomArgEvaluationStatement : Stmt :=
  Stmt.expr
    (Expr.call (Expr.ident "require")
      [ Arg.positional (Expr.literal (Literal.bool true))
      , Arg.positional
          (Expr.call (Expr.ident "TooSmall")
            [Arg.positional
              (Expr.binary BinaryOp.div
                (Expr.literal (Literal.number "1"))
                (Expr.literal (Literal.number "0")))]) ])

def requireCustomArgEvaluationResult : Option CoreResult :=
  Stmt.eval? 8 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState
      SolidCore.Solidity.Source.State.empty)
    requireCustomArgEvaluationStatement

def eventAbiContract : ContractDecl :=
  { name := "Events"
    items :=
      [ ContractItem.eventDecl
          { name := "Set"
            params :=
              [ { name := some "key"
                  ty := Ty.uint 256
                  indexed := true }
              , { name := some "value"
                  ty := Ty.int 256 } ] }
      , ContractItem.function
          { name := some "emitIt"
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [{ name := some "v", ty := some (Ty.int 256) }]
                      (some (Expr.literal (Literal.number "2")))
                  , Stmt.emitEvent
                      (Expr.call (Expr.ident "Set")
                        [ Arg.positional
                            (Expr.literal (Literal.number "4"))
                        , Arg.positional
                            (Expr.unary UnaryOp.neg (Expr.ident "v")) ]) ]) }
      , ContractItem.function
          { name := some "emitThenRevert"
            body :=
              some
                (Stmt.block
                  [ Stmt.emitEvent
                      (Expr.call (Expr.ident "Set")
                        [ Arg.positional
                            (Expr.literal (Literal.number "9"))
                        , Arg.positional
                            (Expr.literal (Literal.number "10")) ])
                  , Stmt.revertCall
                      (Expr.call (Expr.ident "revert") []) ]) } ] }

def eventAbiCallResult : Option CoreCallResult :=
  ContractDecl.call? 16 eventAbiContract
    (SolidCore.Solidity.Source.CallTarget.name "emitIt")
    SolidCore.Solidity.Source.State.empty []

def eventAbiEmittedLog : Option SolidCore.Solidity.Source.Event := do
  let result ← eventAbiCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      state.events.head?
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def eventAbiExpectedTopics : Option (List Word) := do
  let eventDecl ←
    match eventAbiContract.items with
    | ContractItem.eventDecl event :: _ => some event
    | _ => none
  let coreEvent ← EventDecl.toCore eventDecl
  let topic0 ← coreEvent.topic?
  some [topic0, 4]

def eventAbiExpectedDataBytes : List Byte :=
  SolidCore.Solidity.Source.wordToBytesBE
    SolidCore.Solidity.Source.wordBytes
    (SharedSemantics.signedToWord (-2))

def eventAbiTopicsMatchExpected : Option Bool := do
  let event ← eventAbiEmittedLog
  let expected ← eventAbiExpectedTopics
  some (event.topics == expected)

def eventAbiDataBytesMatchExpected : Option Bool := do
  let event ← eventAbiEmittedLog
  some (event.dataBytes == eventAbiExpectedDataBytes)

def revertedEventRollbackDropsLog : Option Bool := do
  let result ←
    ContractDecl.call? 16 eventAbiContract
      (SolidCore.Solidity.Source.CallTarget.name "emitThenRevert")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state _ =>
      some state.events.isEmpty
  | _ => some false

def revertedEventRollbackPreservesPriorLogs : Option Bool := do
  let emitted ← eventAbiCallResult
  let state ←
    match emitted with
    | SolidCore.Solidity.Source.CallResult.returned state _ => some state
    | SolidCore.Solidity.Source.CallResult.reverted _ _ => none
  let beforeName ← state.events.head?.map (fun event => event.name)
  let result ←
    ContractDecl.call? 16 eventAbiContract
      (SolidCore.Solidity.Source.CallTarget.name "emitThenRevert")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted revertedState _ =>
      match revertedState.events with
      | [event] =>
          some (event.name == beforeName)
      | _ => some false
  | _ => some false

def storageRollbackContract : ContractDecl :=
  { name := "StorageRollback"
    items :=
      [ ContractItem.stateVar
          { name := "x"
            ty := Ty.uint 256
            visibility := some Visibility.public_ }
      , ContractItem.function
          { name := some "set"
            params := [{ name := some "value", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign
                    (Expr.ident "x")
                    AssignOp.assign
                    (Expr.ident "value"))) }
      , ContractItem.function
          { name := some "writeThenRevert"
            params := [{ name := some "value", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign
                        (Expr.ident "x")
                        AssignOp.assign
                        (Expr.ident "value"))
                  , Stmt.revertCall
                      (Expr.call (Expr.ident "revert") []) ]) } ] }

def revertedStorageWriteDropsWrite : Option Bool := do
  let result ←
    ContractDecl.call? 24 storageRollbackContract
      (SolidCore.Solidity.Source.CallTarget.name "writeThenRevert")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 9]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state _ =>
      let getter ←
        ContractDecl.call? 16 storageRollbackContract
          (SolidCore.Solidity.Source.CallTarget.name "x")
          state []
      match getter with
      | SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word value] =>
          some (value == 0)
      | _ => some false
  | _ => some false

def revertedStorageWritePreservesPriorValue : Option Bool := do
  let setResult ←
    ContractDecl.call? 24 storageRollbackContract
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 5]
  let setState ←
    match setResult with
    | SolidCore.Solidity.Source.CallResult.returned state _ => some state
    | SolidCore.Solidity.Source.CallResult.reverted _ _ => none
  let result ←
    ContractDecl.call? 24 storageRollbackContract
      (SolidCore.Solidity.Source.CallTarget.name "writeThenRevert")
      setState [SolidCore.Solidity.Source.Value.word 11]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted revertedState _ =>
      let getter ←
        ContractDecl.call? 16 storageRollbackContract
          (SolidCore.Solidity.Source.CallTarget.name "x")
          revertedState []
      match getter with
      | SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word value] =>
          some (value == 5)
      | _ => some false
  | _ => some false

def selfdestructSourceFunction : FunctionDecl :=
  { name := some "destroy"
    body :=
      some
        (Stmt.block
          [ Stmt.expr
              (Expr.call (Expr.ident "selfdestruct")
                [Arg.positional
                  (Expr.literal (Literal.address 0xbeef))])
          , Stmt.expr
              (Expr.assign (Expr.ident "x") AssignOp.assign
                (Expr.literal (Literal.number "9"))) ]) }

def selfdestructSourceContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    self := 0xcafe
    storageFields := [{ name := "x", slot := 0 }] }

def selfdestructSourceCallResult : Option CoreCallResult :=
  FunctionDecl.call? 16 ["x"] [] selfdestructSourceContext
    SolidCore.Solidity.Source.State.empty selfdestructSourceFunction []

def selfdestructRecordsAndStopsMatches : Option Bool := do
  let result ← selfdestructSourceCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      match state.selfdestructs with
      | [(fromAddress, recipient)] =>
          some
            (SolidCore.Solidity.Source.wordEq fromAddress 0xcafe &&
              SolidCore.Solidity.Source.wordEq recipient 0xbeef &&
              SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0)
      | _ => some false
  | _ => some false

def dynamicEventAbiContract : ContractDecl :=
  { name := "DynamicEvents"
    items :=
      [ ContractItem.eventDecl
          { name := "Blob"
            params :=
              [ { name := some "key"
                  ty := Ty.bytes
                  indexed := true }
              , { name := some "payload"
                  ty := Ty.bytes } ] }
      , ContractItem.function
          { name := some "emitIt"
            body :=
              some
                (Stmt.emitEvent
                  (Expr.call (Expr.ident "Blob")
                    [ Arg.positional
                        (Expr.literal (Literal.bytes [1, 2, 3]))
                    , Arg.positional
                        (Expr.literal (Literal.bytes [4, 5])) ])) } ] }

def dynamicEventAbiCallResult : Option CoreCallResult :=
  ContractDecl.call? 16 dynamicEventAbiContract
    (SolidCore.Solidity.Source.CallTarget.name "emitIt")
    SolidCore.Solidity.Source.State.empty []

def dynamicEventAbiEmittedLog : Option SolidCore.Solidity.Source.Event := do
  let result ← dynamicEventAbiCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      state.events.head?
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def dynamicEventAbiExpectedTopics : Option (List Word) := do
  let eventDecl ←
    match dynamicEventAbiContract.items with
    | ContractItem.eventDecl event :: _ => some event
    | _ => none
  let coreEvent ← EventDecl.toCore eventDecl
  let topic0 ← coreEvent.topic?
  some
    [ topic0
    , SolidCore.Solidity.Source.keccakWord [1, 2, 3] ]

def dynamicEventAbiExpectedDataBytes : Option (List Byte) :=
  SolidCore.Solidity.Source.abiEncodeValues?
    [SolidCore.Solidity.Source.Ty.bytesCalldata]
    [SolidCore.Solidity.Source.Value.bytes [4, 5]]

def dynamicEventAbiTopicsMatchExpected : Option Bool := do
  let event ← dynamicEventAbiEmittedLog
  let expected ← dynamicEventAbiExpectedTopics
  some (event.topics == expected)

def dynamicEventAbiDataBytesMatchExpected : Option Bool := do
  let event ← dynamicEventAbiEmittedLog
  let expected ← dynamicEventAbiExpectedDataBytes
  some (event.dataBytes == expected)

def addressMembersFunction : FunctionDecl :=
  { name := some "accountInfo"
    returns :=
      [ { name := some "selfAddress", ty := Ty.address false }
      , { name := some "selfBalance", ty := Ty.uint 256 }
      , { name := some "otherBalance", ty := Ty.uint 256 }
      , { name := some "otherCodehash", ty := Ty.bytesN 32 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.call (Expr.typeName (Ty.address false))
                    [Arg.positional (Expr.ident "this")])
              , TupleItem.value
                  (Expr.member
                    (Expr.call (Expr.typeName (Ty.address false))
                      [Arg.positional (Expr.ident "this")])
                    "balance")
              , TupleItem.value
                  (Expr.member (Expr.literal (Literal.address 0xbeef))
                    "balance")
              , TupleItem.value
                  (Expr.member (Expr.literal (Literal.address 0xbeef))
                    "codehash") ]))) }

def addressMembersContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    self := 0xcafe
    accountBalances := [(0xcafe, 1000), (0xbeef, 77)]
    accountCodehashes := [(0xbeef, 0x123456)] }

def addressMembersCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] addressMembersContext
    SolidCore.Solidity.Source.State.empty addressMembersFunction []

def addressCodeMemberFunction : FunctionDecl :=
  { name := some "codeInfo"
    returns :=
      [ { name := some "code", ty := Ty.bytes }
      , { name := some "codeLength", ty := Ty.uint 256 }
      , { name := some "missingLength", ty := Ty.uint 256 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.member (Expr.literal (Literal.address 0xbeef))
                    "code")
              , TupleItem.value
                  (Expr.member
                    (Expr.member (Expr.literal (Literal.address 0xbeef))
                      "code")
                    "length")
              , TupleItem.value
                  (Expr.member
                    (Expr.member (Expr.literal (Literal.address 0xdead))
                      "code")
                    "length") ]))) }

def addressCodeMemberContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    accountCodes := [(0xbeef, [1, 2, 3, 4])] }

def addressCodeMemberCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] addressCodeMemberContext
    SolidCore.Solidity.Source.State.empty addressCodeMemberFunction []

def lowLevelCallFunction : FunctionDecl :=
  { name := some "probe"
    params :=
      [ { name := some "target", ty := Ty.address false }
      , { name := some "payload", ty := Ty.bytes } ]
    returns := [{ name := some "out", ty := lowLevelCallReturnTy }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.member (Expr.ident "target") "call")
              [Arg.positional (Expr.ident "payload")]))) }

def lowLevelCallContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    lowLevelCallResults :=
      [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
          target := 0xbeef
          calldata := [1, 2, 3]
          success := true
          output := [9, 8] } ] }

def lowLevelCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] lowLevelCallContext
    SolidCore.Solidity.Source.State.empty lowLevelCallFunction
    [ SolidCore.Solidity.Source.Value.word 0xbeef
    , SolidCore.Solidity.Source.Value.bytes [1, 2, 3] ]

def lowLevelCallMatches : Option Bool := do
  let result ← lowLevelCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] => do
      let (success, output) ← CoreValue.asLowLevelReturn? value
      some
        (SolidCore.Solidity.Source.wordEq success 1 &&
          output == [9, 8])
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => some false
  | _ => none

def lowLevelCallValueFunction : FunctionDecl :=
  { name := some "pay"
    returns := [{ name := some "out", ty := lowLevelCallReturnTy }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.callWithOptions
              (Expr.member (Expr.literal (Literal.address 0xbeef)) "call")
              [ CallOption.named "gas" (Expr.literal (Literal.number "1000000"))
              , CallOption.named "value" (Expr.literal (Literal.number "5")) ]
              [Arg.positional (Expr.literal (Literal.bytes [1, 2]))]))) }

def lowLevelCallValueContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    lowLevelCallResults :=
      [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
          target := 0xbeef
          calldata := [1, 2]
          value := 5
          success := true
          output := [4, 5, 6] } ] }

def lowLevelCallValueResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] lowLevelCallValueContext
    SolidCore.Solidity.Source.State.empty lowLevelCallValueFunction []

def lowLevelCallValueMatches : Option Bool := do
  let result ← lowLevelCallValueResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] => do
      let (success, output) ← CoreValue.asLowLevelReturn? value
      some
        (SolidCore.Solidity.Source.wordEq success 1 &&
          output == [4, 5, 6])
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => some false
  | _ => none

def lowLevelCallOptionGasEffectsFunction : FunctionDecl :=
  { name := some "payWithGasExpr"
    returns :=
      [ { name := some "out", ty := lowLevelCallReturnTy }
      , { name := some "gasSeen", ty := Ty.uint 256 }
      , { name := some "sent", ty := Ty.uint 256 } ]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [{ name := some "gasSeen", ty := some (Ty.uint 256) }]
              (some (Expr.literal (Literal.number "0")))
          , Stmt.varDecl
              [{ name := some "sent", ty := some (Ty.uint 256) }]
              (some (Expr.literal (Literal.number "0")))
          , Stmt.returnValues
              (some
                (Expr.tuple
                  [ TupleItem.value
                      (Expr.callWithOptions
                        (Expr.member
                          (Expr.literal (Literal.address 0xbeef)) "call")
                        [ CallOption.named "gas"
                            (Expr.assign (Expr.ident "gasSeen")
                              AssignOp.assign
                              (Expr.literal (Literal.number "11")))
                        , CallOption.named "value"
                            (Expr.assign (Expr.ident "sent")
                              AssignOp.assign
                              (Expr.literal (Literal.number "5"))) ]
                        [Arg.positional
                          (Expr.literal (Literal.bytes [1, 2]))])
                  , TupleItem.value (Expr.ident "gasSeen")
                  , TupleItem.value (Expr.ident "sent") ])) ]) }

def lowLevelCallOptionGasEffectsContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    lowLevelCallResults :=
      [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
          target := 0xbeef
          calldata := [1, 2]
          value := 5
          success := true
          output := [4, 5, 6] } ] }

def lowLevelCallOptionGasEffectsResult : Option CoreCallResult :=
  FunctionDecl.call? 16 [] [] lowLevelCallOptionGasEffectsContext
    SolidCore.Solidity.Source.State.empty
    lowLevelCallOptionGasEffectsFunction []

def lowLevelCallOptionGasEffectsMatches : Option Bool := do
  let result ← lowLevelCallOptionGasEffectsResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [value, SolidCore.Solidity.Source.Value.word gasSeen,
        SolidCore.Solidity.Source.Value.word sent] => do
      let (success, output) ← CoreValue.asLowLevelReturn? value
      some
        (SolidCore.Solidity.Source.wordEq success 1 &&
          output == [4, 5, 6] &&
          gasSeen == 11 &&
          sent == 5)
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => some false
  | _ => none

def lowLevelStaticDelegateFunction : FunctionDecl :=
  { name := some "probeBoth"
    params :=
      [ { name := some "target", ty := Ty.address false }
      , { name := some "payload", ty := Ty.bytes } ]
    returns :=
      [ { name := some "staticOut", ty := lowLevelCallReturnTy }
      , { name := some "delegateOut", ty := lowLevelCallReturnTy } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.callWithOptions
                    (Expr.member (Expr.ident "target") "staticcall")
                    [CallOption.named "gas"
                      (Expr.literal (Literal.number "50000"))]
                    [Arg.positional (Expr.ident "payload")])
              , TupleItem.value
                  (Expr.call
                    (Expr.member (Expr.ident "target") "delegatecall")
                    [Arg.positional (Expr.ident "payload")]) ]))) }

def lowLevelStaticDelegateContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    lowLevelCallResults :=
      [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
          target := 0xcafe
          calldata := [7, 7]
          success := true
          output := [1] }
      , { kind := SolidCore.Solidity.Source.LowLevelCallKind.delegatecall
          target := 0xcafe
          calldata := [7, 7]
          success := false
          output := [2, 3] } ] }

def lowLevelStaticDelegateResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] lowLevelStaticDelegateContext
    SolidCore.Solidity.Source.State.empty lowLevelStaticDelegateFunction
    [ SolidCore.Solidity.Source.Value.word 0xcafe
    , SolidCore.Solidity.Source.Value.bytes [7, 7] ]

def lowLevelStaticDelegateMatches : Option Bool := do
  let result ← lowLevelStaticDelegateResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [staticValue, delegateValue] => do
      let (staticSuccess, staticOutput) ←
        CoreValue.asLowLevelReturn? staticValue
      let (delegateSuccess, delegateOutput) ←
        CoreValue.asLowLevelReturn? delegateValue
      some
        (SolidCore.Solidity.Source.wordEq staticSuccess 1 &&
          staticOutput == [1] &&
          SolidCore.Solidity.Source.wordEq delegateSuccess 0 &&
          delegateOutput == [2, 3])
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => some false
  | _ => none

def lowLevelStaticCallOptionGasEffectsFunction : FunctionDecl :=
  { name := some "staticGasExpr"
    params :=
      [ { name := some "target", ty := Ty.address false }
      , { name := some "payload", ty := Ty.bytes } ]
    returns :=
      [ { name := some "out", ty := lowLevelCallReturnTy }
      , { name := some "gasSeen", ty := Ty.uint 256 } ]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [{ name := some "gasSeen", ty := some (Ty.uint 256) }]
              (some (Expr.literal (Literal.number "0")))
          , Stmt.returnValues
              (some
                (Expr.tuple
                  [ TupleItem.value
                      (Expr.callWithOptions
                        (Expr.member (Expr.ident "target") "staticcall")
                        [CallOption.named "gas"
                          (Expr.assign (Expr.ident "gasSeen")
                            AssignOp.assign
                            (Expr.literal (Literal.number "12")))]
                        [Arg.positional (Expr.ident "payload")])
                  , TupleItem.value (Expr.ident "gasSeen") ])) ]) }

def lowLevelStaticCallOptionGasEffectsContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with
    lowLevelCallResults :=
      [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.staticcall
          target := 0xcafe
          calldata := [7, 7]
          value := 0
          success := true
          output := [1] } ] }

def lowLevelStaticCallOptionGasEffectsResult : Option CoreCallResult :=
  FunctionDecl.call? 16 [] []
    lowLevelStaticCallOptionGasEffectsContext
    SolidCore.Solidity.Source.State.empty
    lowLevelStaticCallOptionGasEffectsFunction
    [ SolidCore.Solidity.Source.Value.word 0xcafe
    , SolidCore.Solidity.Source.Value.bytes [7, 7] ]

def lowLevelStaticCallOptionGasEffectsMatches : Option Bool := do
  let result ← lowLevelStaticCallOptionGasEffectsResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [value, SolidCore.Solidity.Source.Value.word gasSeen] => do
      let (success, output) ← CoreValue.asLowLevelReturn? value
      some
        (SolidCore.Solidity.Source.wordEq success 1 &&
          output == [1] &&
          gasSeen == 12)
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => some false
  | _ => none

def lowLevelMissingResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty lowLevelCallFunction
    [ SolidCore.Solidity.Source.Value.word 0xbeef
    , SolidCore.Solidity.Source.Value.bytes [1, 2, 3] ]

def lowLevelMissingResultMatches : Option Bool := do
  let result ← lowLevelMissingResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] => do
      let (success, output) ← CoreValue.asLowLevelReturn? value
      some
        (SolidCore.Solidity.Source.wordEq success 0 &&
          output == [])
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => some false
  | _ => none

def lowLevelCallAbiTyMatches : Bool :=
  match
    Expr.abiTy? []
      (Expr.call (Expr.member (Expr.ident "target") "call")
        [Arg.positional (Expr.ident "payload")])
  with
  | some (Ty.tuple [Ty.bool, Ty.bytes]) => true
  | _ => false

def concatBuiltinsFunction : FunctionDecl :=
  { name := some "join"
    params :=
      [ { name := some "prefix", ty := Ty.bytes }
      , { name := some "suffix", ty := Ty.string } ]
    returns :=
      [ { name := some "joinedBytes", ty := Ty.bytes }
      , { name := some "joinedString", ty := Ty.string } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.call
                    (Expr.member (Expr.ident "bytes") "concat")
                    [ Arg.positional (Expr.ident "prefix")
                    , Arg.positional (Expr.literal (Literal.bytes [3, 4])) ])
              , TupleItem.value
                  (Expr.call
                    (Expr.member (Expr.ident "string") "concat")
                    [ Arg.positional (Expr.literal (Literal.string "hi"))
                    , Arg.positional (Expr.ident "suffix") ]) ]))) }

def concatBuiltinsCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty concatBuiltinsFunction
    [ SolidCore.Solidity.Source.Value.bytes [1, 2]
    , SolidCore.Solidity.Source.Value.bytes ("!".toList.map Char.toNat) ]

def bytesConcatFixedFunction : FunctionDecl :=
  { name := some "joinFixed"
    params := [{ name := some "tail", ty := Ty.bytes }]
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call
              (Expr.member (Expr.ident "bytes") "concat")
              [ Arg.positional
                  (Expr.call (Expr.typeName (Ty.bytesN 1))
                    [Arg.positional
                      (Expr.literal (Literal.number "0xaa"))])
              , Arg.positional
                  (Expr.call (Expr.typeName (Ty.bytesN 2))
                    [Arg.positional
                      (Expr.literal (Literal.number "0xbbcc"))])
              , Arg.positional (Expr.literal (Literal.string "Hi"))
              , Arg.positional (Expr.ident "tail") ]))) }

def bytesConcatFixedCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty bytesConcatFixedFunction
    [SolidCore.Solidity.Source.Value.bytes [1, 2]]

def bytesConcatFixedMatchesExpected : Option Bool := do
  let result ← bytesConcatFixedCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      some (bytes == [0xaa, 0xbb, 0xcc, 72, 105, 1, 2])
  | _ => some false

def bytesConcatRejected : Bool :=
  (match
      Expr.toCore? []
        (Expr.call (Expr.member (Expr.ident "bytes") "concat")
          [Arg.positional (Expr.literal (Literal.number "1"))])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.member (Expr.ident "bytes") "concat")
          [Arg.named "x" (Expr.literal (Literal.bytes [1]))])
    with
    | none => true
    | some _ => false)

def stringConcatUnicodeFunction : FunctionDecl :=
  { name := some "joinString"
    params := [{ name := some "suffix", ty := Ty.string }]
    returns := [{ name := some "out", ty := Ty.string }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call
              (Expr.member (Expr.ident "string") "concat")
              [ Arg.positional (Expr.literal (Literal.string "a"))
              , Arg.positional (Expr.literal (Literal.unicodeString "é"))
              , Arg.positional (Expr.ident "suffix") ]))) }

def stringConcatUnicodeCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty stringConcatUnicodeFunction
    [SolidCore.Solidity.Source.Value.bytes ("!".toList.map Char.toNat)]

def stringConcatUnicodeMatchesExpected : Option Bool := do
  let result ← stringConcatUnicodeCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      some (bytes == [97, 0xc3, 0xa9, 33])
  | _ => some false

def stringConcatRejected : Bool :=
  (match
      Expr.toCore? []
        (Expr.call (Expr.member (Expr.ident "string") "concat")
          [Arg.positional (Expr.literal (Literal.bytes [1]))])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.member (Expr.ident "string") "concat")
          [Arg.positional
            (Expr.call (Expr.typeName (Ty.bytesN 1))
              [Arg.positional
                (Expr.literal (Literal.number "0xaa"))])])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.member (Expr.ident "string") "concat")
          [Arg.named "x" (Expr.literal (Literal.string "x"))])
    with
    | none => true
    | some _ => false)

def bytesSliceFunction : FunctionDecl :=
  { name := some "sliceIt"
    params := [{ name := some "input", ty := Ty.bytes }]
    returns :=
      [ { name := some "middle", ty := Ty.bytes }
      , { name := some "tail", ty := Ty.bytes }
      , { name := some "head", ty := Ty.bytes }
      , { name := some "relative", ty := Ty.uint 256 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.slice (Expr.ident "input")
                    (some (Expr.literal (Literal.number "1")))
                    (some (Expr.literal (Literal.number "4"))))
              , TupleItem.value
                  (Expr.slice (Expr.ident "input")
                    (some (Expr.literal (Literal.number "3"))) none)
              , TupleItem.value
                  (Expr.slice (Expr.ident "input") none
                    (some (Expr.literal (Literal.number "2"))))
              , TupleItem.value
                  (Expr.index
                    (Expr.slice (Expr.ident "input")
                      (some (Expr.literal (Literal.number "1")))
                      (some (Expr.literal (Literal.number "4"))))
                    (Expr.literal (Literal.number "0"))) ]))) }

def bytesSliceCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty bytesSliceFunction
    [SolidCore.Solidity.Source.Value.bytes [10, 20, 30, 40, 50]]

def bytesSliceOutOfBoundsStatement : Stmt :=
  Stmt.returnValues
    (some
      (Expr.slice (Expr.literal (Literal.bytes [1, 2]))
        (some (Expr.literal (Literal.number "2")))
        (some (Expr.literal (Literal.number "1")))))

def bytesSliceOutOfBoundsResult : Option CoreResult :=
  Stmt.eval? 8 [] SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState
      SolidCore.Solidity.Source.State.empty)
    bytesSliceOutOfBoundsStatement

def stringLiteralFunction : FunctionDecl :=
  { name := some "hello"
    returns := [{ name := some "out", ty := Ty.string }]
    body :=
      some
        (Stmt.returnValues
          (some (Expr.literal (Literal.string "hi")))) }

def stringLiteralContract : ContractDecl :=
  { name := "Strings"
    items := [ContractItem.function stringLiteralFunction] }

def stringLiteralCallResult : Option CoreCallResult :=
  ContractDecl.call? 8 stringLiteralContract
    (SolidCore.Solidity.Source.CallTarget.name "hello")
    SolidCore.Solidity.Source.State.empty []

def stringLiteralCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? stringLiteralContract
  let function ← contract.findFunctionByName? "hello"
  let calldata ← SolidCore.Solidity.Source.ABI.calldataFor? function []
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    8 contract SolidCore.Solidity.Source.State.empty calldata

def numericLiteralFunction : FunctionDecl :=
  { name := some "numbers"
    returns :=
      [ { name := some "hexValue", ty := Ty.uint 256 }
      , { name := some "decimalValue", ty := Ty.uint 256 }
      , { name := some "separatedHexValue", ty := Ty.uint 256 }
      , { name := some "upperHexValue", ty := Ty.uint 256 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.literal (Literal.number "0xff"))
              , TupleItem.value
                  (Expr.literal (Literal.number "123_000"))
              , TupleItem.value
                  (Expr.literal (Literal.number "0x2e_ff"))
              , TupleItem.value
                  (Expr.literal (Literal.number "0X2a")) ]))) }

def numericLiteralCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty numericLiteralFunction []

def numericLiteralMatchesExpected : Option Bool := do
  let result ← numericLiteralCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word hexValue
      , SolidCore.Solidity.Source.Value.word decimalValue
      , SolidCore.Solidity.Source.Value.word separatedHexValue
      , SolidCore.Solidity.Source.Value.word upperHexValue ] =>
      some (hexValue == 255 && decimalValue == 123000 &&
        separatedHexValue == 12031 && upperHexValue == 42)
  | _ => some false

def malformedNumericLiteralsRejected : Bool :=
  (match Literal.toCoreExpr? (Literal.number "0x_ff") with
    | none => true
    | some _ => false) &&
  (match Literal.toCoreExpr? (Literal.number "12__3") with
    | none => true
    | some _ => false) &&
  (match Literal.toCoreExpr? (Literal.number "012") with
    | none => true
    | some _ => false)

def scaledNumericLiteralFunction : FunctionDecl :=
  { name := some "scaledNumbers"
    returns :=
      [ { name := some "scientific", ty := Ty.uint 256 }
      , { name := some "fractionalExponent", ty := Ty.uint 256 }
      , { name := some "leadingDotExponent", ty := Ty.uint 256 }
      , { name := some "negativeExponentExact", ty := Ty.uint 256 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.literal (Literal.number "2e10"))
              , TupleItem.value
                  (Expr.literal (Literal.number "2.5e1"))
              , TupleItem.value
                  (Expr.literal (Literal.number ".5e1"))
              , TupleItem.value
                  (Expr.literal (Literal.number "120e-1")) ]))) }

def scaledNumericLiteralCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty scaledNumericLiteralFunction []

def scaledNumericLiteralMatchesExpected : Option Bool := do
  let result ← scaledNumericLiteralCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word scientific
      , SolidCore.Solidity.Source.Value.word fractionalExponent
      , SolidCore.Solidity.Source.Value.word leadingDotExponent
      , SolidCore.Solidity.Source.Value.word negativeExponentExact ] =>
      some (scientific == 20000000000 &&
        fractionalExponent == 25 &&
        leadingDotExponent == 5 &&
        negativeExponentExact == 12)
  | _ => some false

def nonIntegralNumericLiteralsRejected : Bool :=
  (match Literal.toCoreExpr? (Literal.number "2.5") with
    | none => true
    | some _ => false) &&
  (match Literal.toCoreExpr? (Literal.number ".5") with
    | none => true
    | some _ => false) &&
  (match Literal.toCoreExpr? (Literal.number "1e-1") with
    | none => true
    | some _ => false)

def numberLiteralExpressionFunction : FunctionDecl :=
  { name := some "literalExpressions"
    returns :=
      [ { name := some "halfTimesEight", ty := Ty.uint 256 }
      , { name := some "dividedThenAdded", ty := Ty.uint 256 }
      , { name := some "fractionalPowerScaled", ty := Ty.uint 256 }
      , { name := some "halfLessThanOne", ty := Ty.bool }
      , { name := some "ratioEquality", ty := Ty.bool } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.binary BinaryOp.mul
                    (Expr.literal (Literal.number ".5"))
                    (Expr.literal (Literal.number "8")))
              , TupleItem.value
                  (Expr.binary BinaryOp.add
                    (Expr.binary BinaryOp.div
                      (Expr.literal (Literal.number "5"))
                      (Expr.literal (Literal.number "2")))
                    (Expr.literal (Literal.number ".5")))
              , TupleItem.value
                  (Expr.binary BinaryOp.mul
                    (Expr.binary BinaryOp.exp
                      (Expr.literal (Literal.number ".5"))
                      (Expr.literal (Literal.number "2")))
                    (Expr.literal (Literal.number "16")))
              , TupleItem.value
                  (Expr.binary BinaryOp.lt
                    (Expr.literal (Literal.number ".5"))
                    (Expr.literal (Literal.number "1")))
              , TupleItem.value
                  (Expr.binary BinaryOp.eq
                    (Expr.literal (Literal.number "2.5"))
                    (Expr.binary BinaryOp.div
                      (Expr.literal (Literal.number "5"))
                      (Expr.literal (Literal.number "2")))) ]))) }

def numberLiteralExpressionCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    numberLiteralExpressionFunction []

def numberLiteralExpressionMatchesExpected : Option Bool := do
  let result ← numberLiteralExpressionCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word halfTimesEight
      , SolidCore.Solidity.Source.Value.word dividedThenAdded
      , SolidCore.Solidity.Source.Value.word fractionalPowerScaled
      , SolidCore.Solidity.Source.Value.word halfLessThanOne
      , SolidCore.Solidity.Source.Value.word ratioEquality ] =>
      some (halfTimesEight == 4 &&
        dividedThenAdded == 3 &&
        fractionalPowerScaled == 4 &&
        halfLessThanOne == 1 &&
        ratioEquality == 1)
  | _ => some false

def nonIntegralNumberLiteralExpressionRejected : Bool :=
  match
    Expr.toCore? []
      (Expr.binary BinaryOp.mul
        (Expr.literal (Literal.number ".5"))
        (Expr.literal (Literal.number "7")))
  with
  | none => true
  | some _ => false

def unitNumberLiteralFunction : FunctionDecl :=
  { name := some "unitNumbers"
    returns :=
      [ { name := some "oneWei", ty := Ty.uint 256 }
      , { name := some "oneGwei", ty := Ty.uint 256 }
      , { name := some "oneEther", ty := Ty.uint 256 }
      , { name := some "twoPointFiveEther", ty := Ty.uint 256 }
      , { name := some "twoMinutes", ty := Ty.uint 256 }
      , { name := some "oneWeek", ty := Ty.uint 256 }
      , { name := some "timeEquality", ty := Ty.bool }
      , { name := some "typedDays", ty := Ty.uint 32 }
      , { name := some "payableZero", ty := Ty.address true } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.literal
                    (Literal.unitNumber "1" UnitDenomination.wei))
              , TupleItem.value
                  (Expr.literal
                    (Literal.unitNumber "1" UnitDenomination.gwei))
              , TupleItem.value
                  (Expr.literal
                    (Literal.unitNumber "1" UnitDenomination.ether))
              , TupleItem.value
                  (Expr.literal
                    (Literal.unitNumber "2.5" UnitDenomination.ether))
              , TupleItem.value
                  (Expr.literal
                    (Literal.unitNumber "2" UnitDenomination.minutes))
              , TupleItem.value
                  (Expr.literal
                    (Literal.unitNumber "1" UnitDenomination.weeks))
              , TupleItem.value
                  (Expr.binary BinaryOp.eq
                    (Expr.literal
                      (Literal.unitNumber "1" UnitDenomination.days))
                    (Expr.literal
                      (Literal.unitNumber "24" UnitDenomination.hours)))
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.uint 32))
                    [Arg.positional
                      (Expr.literal
                        (Literal.unitNumber "1" UnitDenomination.days))])
              , TupleItem.value
                  (Expr.payableConversion
                    (Expr.literal
                      (Literal.unitNumber "0" UnitDenomination.wei))) ]))) }

def unitNumberLiteralCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty unitNumberLiteralFunction []

def unitNumberLiteralMatchesExpected : Option Bool := do
  let result ← unitNumberLiteralCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word oneWei
      , SolidCore.Solidity.Source.Value.word oneGwei
      , SolidCore.Solidity.Source.Value.word oneEther
      , SolidCore.Solidity.Source.Value.word twoPointFiveEther
      , SolidCore.Solidity.Source.Value.word twoMinutes
      , SolidCore.Solidity.Source.Value.word oneWeek
      , SolidCore.Solidity.Source.Value.word timeEquality
      , SolidCore.Solidity.Source.Value.word typedDays
      , SolidCore.Solidity.Source.Value.word payableZero ] =>
      some (oneWei == 1 &&
        oneGwei == 1000000000 &&
        oneEther == 1000000000000000000 &&
        twoPointFiveEther == 2500000000000000000 &&
        twoMinutes == 120 &&
        oneWeek == 604800 &&
        timeEquality == 1 &&
        typedDays == 86400 &&
        payableZero == 0)
  | _ => some false

def unitNumberLiteralRejected : Bool :=
  (match
      Expr.toCore? []
        (Expr.literal
          (Literal.unitNumber ".5" UnitDenomination.wei))
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.literal
          (Literal.unitNumber "1e-19" UnitDenomination.ether))
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.uint 8))
          [Arg.positional
            (Expr.literal
              (Literal.unitNumber "1" UnitDenomination.ether))])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.payableConversion
          (Expr.literal
            (Literal.unitNumber "1" UnitDenomination.wei)))
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.bytesN 4))
          [Arg.positional
            (Expr.literal
              (Literal.unitNumber "1" UnitDenomination.wei))])
    with
    | none => true
    | some _ => false)

def typedNumericLiteralConversionFunction : FunctionDecl :=
  { name := some "typedLiteralConversions"
    returns :=
      [ { name := some "negativeSmall", ty := Ty.int 8 }
      , { name := some "negativeMin", ty := Ty.int 8 }
      , { name := some "positiveMax", ty := Ty.uint 8 }
      , { name := some "foldedInt", ty := Ty.int 8 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.call (Expr.typeName (Ty.int 8))
                    [Arg.positional
                      (Expr.unary UnaryOp.neg
                        (Expr.literal (Literal.number "5")))])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.int 8))
                    [Arg.positional
                      (Expr.unary UnaryOp.neg
                        (Expr.literal (Literal.number "128")))])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.uint 8))
                    [Arg.positional
                      (Expr.literal (Literal.number "255"))])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.int 8))
                    [Arg.positional
                      (Expr.binary BinaryOp.mul
                        (Expr.literal (Literal.number ".5"))
                        (Expr.literal (Literal.number "8")))]) ]))) }

def typedNumericLiteralConversionCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    typedNumericLiteralConversionFunction []

def typedNumericLiteralConversionMatchesExpected : Option Bool := do
  let result ← typedNumericLiteralConversionCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.int negativeSmall
      , SolidCore.Solidity.Source.Value.int negativeMin
      , SolidCore.Solidity.Source.Value.word positiveMax
      , SolidCore.Solidity.Source.Value.int foldedInt ] =>
      some (SharedSemantics.signedValue negativeSmall = -5 &&
        SharedSemantics.signedValue negativeMin = -128 &&
        positiveMax == 255 &&
        SharedSemantics.signedValue foldedInt = 4)
  | _ => some false

def numericLiteralCastBoundsRejected : Bool :=
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.uint 8))
          [Arg.positional (Expr.literal (Literal.number "256"))])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.int 8))
          [Arg.positional (Expr.literal (Literal.number "128"))])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.int 8))
          [Arg.positional
            (Expr.unary UnaryOp.neg
              (Expr.literal (Literal.number "129")))])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.uint 8))
          [Arg.positional
            (Expr.unary UnaryOp.neg
              (Expr.literal (Literal.number "1")))])
    with
    | none => true
    | some _ => false)

def typedNumericLiteralVarDeclFunction : FunctionDecl :=
  { name := some "typedLiteralVars"
    returns :=
      [ { name := some "negative", ty := Ty.int 8 }
      , { name := some "folded", ty := Ty.uint 8 } ]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [ { name := some "negative", ty := some (Ty.int 8) } ]
              (some
                (Expr.unary UnaryOp.neg
                  (Expr.literal (Literal.number "5"))))
          , Stmt.varDecl
              [ { name := some "folded", ty := some (Ty.uint 8) } ]
              (some
                (Expr.binary BinaryOp.mul
                  (Expr.literal (Literal.number ".5"))
                  (Expr.literal (Literal.number "8"))))
          , Stmt.returnValues
              (some
                (Expr.tuple
                  [ TupleItem.value (Expr.ident "negative")
                  , TupleItem.value (Expr.ident "folded") ])) ]) }

def typedNumericLiteralVarDeclCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    typedNumericLiteralVarDeclFunction []

def typedNumericLiteralVarDeclMatchesExpected : Option Bool := do
  let result ← typedNumericLiteralVarDeclCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.int negative
      , SolidCore.Solidity.Source.Value.word folded ] =>
      some (SharedSemantics.signedValue negative = -5 &&
        folded == 4)
  | _ => some false

def runtimeIntegerCastFunction : FunctionDecl :=
  { name := some "runtimeIntegerCasts"
    params :=
      [ { name := some "x", ty := Ty.uint 256 }
      , { name := some "signed", ty := Ty.int 256 } ]
    returns :=
      [ { name := some "low8", ty := Ty.uint 8 }
      , { name := some "low16", ty := Ty.uint 16 }
      , { name := some "signedLow", ty := Ty.int 8 }
      , { name := some "signedAsUint", ty := Ty.uint 256 }
      , { name := some "fromBytes", ty := Ty.uint 16 }
      , { name := some "fromAddress", ty := Ty.uint 160 }
      , { name := some "roundTripAddress", ty := Ty.address false } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.call (Expr.typeName (Ty.uint 8))
                    [Arg.positional (Expr.ident "x")])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.uint 16))
                    [Arg.positional (Expr.ident "x")])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.int 8))
                    [Arg.positional
                      (Expr.call (Expr.typeName (Ty.uint 8))
                        [Arg.positional (Expr.ident "x")])])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.uint 256))
                    [Arg.positional (Expr.ident "signed")])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.uint 16))
                    [Arg.positional
                      (Expr.call (Expr.typeName (Ty.bytesN 2))
                        [Arg.positional
                          (Expr.literal (Literal.number "0xabcd"))])])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.uint 160))
                    [Arg.positional
                      (Expr.literal (Literal.address 0xbeef))])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.address false))
                    [Arg.positional
                      (Expr.call (Expr.typeName (Ty.uint 160))
                        [Arg.positional (Expr.ident "x")])]) ]))) }

def runtimeIntegerCastCallResult : Option CoreCallResult :=
  FunctionDecl.call? 16 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty runtimeIntegerCastFunction
    [ SolidCore.Solidity.Source.Value.word 0x123456ff
    , SolidCore.Solidity.Source.Value.int
        (SharedSemantics.signedToWord (-3)) ]

def runtimeIntegerCastsMatch : Option Bool := do
  let result ← runtimeIntegerCastCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word low8
      , SolidCore.Solidity.Source.Value.word low16
      , SolidCore.Solidity.Source.Value.int signedLow
      , SolidCore.Solidity.Source.Value.word signedAsUint
      , SolidCore.Solidity.Source.Value.word fromBytes
      , SolidCore.Solidity.Source.Value.word fromAddress
      , SolidCore.Solidity.Source.Value.word roundTripAddress ] =>
      some (low8 == 0xff &&
        low16 == 0x56ff &&
        SharedSemantics.signedValue signedLow = -1 &&
        signedAsUint == SharedSemantics.signedToWord (-3) &&
        fromBytes == 0xabcd &&
        fromAddress == 0xbeef &&
        roundTripAddress == 0x123456ff)
  | _ => some false

def runtimeIntegerCastRejected : Bool :=
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.uint 8))
          [Arg.positional
            (Expr.call (Expr.typeName (Ty.bytesN 2))
              [Arg.positional
                (Expr.literal (Literal.number "0xabcd"))])])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.int 160))
          [Arg.positional
            (Expr.literal (Literal.address 0xbeef))])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.uint 256))
          [Arg.positional
            (Expr.literal (Literal.address 0xbeef))])
    with
    | none => true
    | some _ => false)

def fixedBytesWordBytes (size : Nat) (word : Word) : List Byte :=
  SolidCore.Solidity.Source.wordToBytesBE size word

def fixedBytesLiteralConversionFunction : FunctionDecl :=
  { name := some "fixedByteLiterals"
    returns :=
      [ { name := some "fromHexString", ty := Ty.bytesN 2 }
      , { name := some "fromString", ty := Ty.bytesN 2 }
      , { name := some "fromHexNumber", ty := Ty.bytesN 2 }
      , { name := some "fromZero", ty := Ty.bytesN 4 }
      , { name := some "fromVarDecl", ty := Ty.bytesN 3 } ]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [ { name := some "tag", ty := some (Ty.bytesN 3) } ]
              (some (Expr.literal (Literal.hexString "ab")))
          , Stmt.returnValues
              (some
                (Expr.tuple
                  [ TupleItem.value
                      (Expr.call (Expr.typeName (Ty.bytesN 2))
                        [Arg.positional
                          (Expr.literal (Literal.hexString "12"))])
                  , TupleItem.value
                      (Expr.call (Expr.typeName (Ty.bytesN 2))
                        [Arg.positional
                          (Expr.literal (Literal.string "x"))])
                  , TupleItem.value
                      (Expr.call (Expr.typeName (Ty.bytesN 2))
                        [Arg.positional
                          (Expr.literal (Literal.number "0x1234"))])
                  , TupleItem.value
                      (Expr.call (Expr.typeName (Ty.bytesN 4))
                        [Arg.positional
                          (Expr.literal (Literal.number "0"))])
                  , TupleItem.value (Expr.ident "tag") ])) ]) }

def fixedBytesLiteralConversionCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    fixedBytesLiteralConversionFunction []

def fixedBytesLiteralConversionMatchesExpected : Option Bool := do
  let result ← fixedBytesLiteralConversionCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word fromHexString
      , SolidCore.Solidity.Source.Value.word fromString
      , SolidCore.Solidity.Source.Value.word fromHexNumber
      , SolidCore.Solidity.Source.Value.word fromZero
      , SolidCore.Solidity.Source.Value.word fromVarDecl ] =>
      some (fixedBytesWordBytes 2 fromHexString == [0x12, 0] &&
        fixedBytesWordBytes 2 fromString == [Char.toNat 'x', 0] &&
        fixedBytesWordBytes 2 fromHexNumber == [0x12, 0x34] &&
        fixedBytesWordBytes 4 fromZero == [0, 0, 0, 0] &&
        fixedBytesWordBytes 3 fromVarDecl == [0xab, 0, 0])
  | _ => some false

def fixedBytesLiteralConversionRejected : Bool :=
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.bytesN 2))
          [Arg.positional
            (Expr.literal (Literal.hexString "aabbcc"))])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.bytesN 2))
          [Arg.positional
            (Expr.literal (Literal.string "xyz"))])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.bytesN 2))
          [Arg.positional
            (Expr.literal (Literal.number "0x123"))])
    with
    | none => true
    | some _ => false)

def fixedBytesMembersFunction : FunctionDecl :=
  { name := some "fixedBytesMembers"
    returns :=
      [ { name := some "len", ty := Ty.uint 256 }
      , { name := some "first", ty := Ty.bytesN 1 }
      , { name := some "second", ty := Ty.bytesN 1 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.member
                    (Expr.call (Expr.typeName (Ty.bytesN 2))
                      [Arg.positional
                        (Expr.literal (Literal.number "0xaabb"))])
                    "length")
              , TupleItem.value
                  (Expr.index
                    (Expr.call (Expr.typeName (Ty.bytesN 2))
                      [Arg.positional
                        (Expr.literal (Literal.number "0xaabb"))])
                    (Expr.literal (Literal.number "0")))
              , TupleItem.value
                  (Expr.index
                    (Expr.call (Expr.typeName (Ty.bytesN 2))
                      [Arg.positional
                        (Expr.literal (Literal.number "0xaabb"))])
                    (Expr.literal (Literal.number "1"))) ]))) }

def fixedBytesMembersCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty fixedBytesMembersFunction []

def fixedBytesMembersMatchesExpected : Option Bool := do
  let result ← fixedBytesMembersCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word len
      , SolidCore.Solidity.Source.Value.word first
      , SolidCore.Solidity.Source.Value.word second ] =>
      some (len == 2 && first == 0xaa && second == 0xbb)
  | _ => some false

def fixedBytesIndexOutOfBoundsFunction : FunctionDecl :=
  { name := some "fixedBytesIndexOutOfBounds"
    returns := [{ name := some "out", ty := Ty.bytesN 1 }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.index
              (Expr.call (Expr.typeName (Ty.bytesN 2))
                [Arg.positional
                  (Expr.literal (Literal.number "0xaabb"))])
              (Expr.literal (Literal.number "2"))))) }

def fixedBytesIndexOutOfBoundsPanics : Option Bool := do
  let result ←
    FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty
      fixedBytesIndexOutOfBoundsFunction []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      some (code == 0x32)
  | _ => some false

def fixedBytesRuntimeConversionFunction : FunctionDecl :=
  { name := some "fixedBytesRuntimeConversions"
    params :=
      [ { name := some "longData", ty := Ty.bytes }
      , { name := some "shortData", ty := Ty.bytes } ]
    returns :=
      [ { name := some "wide", ty := Ty.bytesN 4 }
      , { name := some "narrow", ty := Ty.bytesN 1 }
      , { name := some "fromUint", ty := Ty.bytesN 2 }
      , { name := some "fromAddress", ty := Ty.bytesN 20 }
      , { name := some "fromLongData", ty := Ty.bytesN 4 }
      , { name := some "fromShortData", ty := Ty.bytesN 4 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.call (Expr.typeName (Ty.bytesN 4))
                    [Arg.positional
                      (Expr.call (Expr.typeName (Ty.bytesN 2))
                        [Arg.positional
                          (Expr.literal (Literal.number "0x1234"))])])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.bytesN 1))
                    [Arg.positional
                      (Expr.call (Expr.typeName (Ty.bytesN 2))
                        [Arg.positional
                          (Expr.literal (Literal.number "0x1234"))])])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.bytesN 2))
                    [Arg.positional
                      (Expr.call (Expr.typeName (Ty.uint 16))
                        [Arg.positional
                          (Expr.literal (Literal.number "0xabcd"))])])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.bytesN 20))
                    [Arg.positional
                      (Expr.literal (Literal.address 0xbeef))])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.bytesN 4))
                    [Arg.positional (Expr.ident "longData")])
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.bytesN 4))
                    [Arg.positional (Expr.ident "shortData")]) ]))) }

def fixedBytesRuntimeConversionCallResult : Option CoreCallResult :=
  FunctionDecl.call? 16 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    fixedBytesRuntimeConversionFunction
    [ SolidCore.Solidity.Source.Value.bytes [1, 2, 3, 4, 5]
    , SolidCore.Solidity.Source.Value.bytes [9, 8] ]

def fixedBytesRuntimeConversionsMatch : Option Bool := do
  let result ← fixedBytesRuntimeConversionCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word wide
      , SolidCore.Solidity.Source.Value.word narrow
      , SolidCore.Solidity.Source.Value.word fromUint
      , SolidCore.Solidity.Source.Value.word fromAddress
      , SolidCore.Solidity.Source.Value.word fromLongData
      , SolidCore.Solidity.Source.Value.word fromShortData ] =>
      some (fixedBytesWordBytes 4 wide == [0x12, 0x34, 0, 0] &&
        fixedBytesWordBytes 1 narrow == [0x12] &&
        fixedBytesWordBytes 2 fromUint == [0xab, 0xcd] &&
        fixedBytesWordBytes 20 fromAddress ==
          (List.replicate 18 0 ++ [0xbe, 0xef]) &&
        fixedBytesWordBytes 4 fromLongData == [1, 2, 3, 4] &&
        fixedBytesWordBytes 4 fromShortData == [9, 8, 0, 0])
  | _ => some false

def fixedBytesRuntimeConversionRejected : Bool :=
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.bytesN 2))
          [Arg.positional
            (Expr.call (Expr.typeName (Ty.uint 32))
              [Arg.positional
                (Expr.literal (Literal.number "1"))])])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.bytesN 2))
          [Arg.positional
            (Expr.literal (Literal.address 0xbeef))])
    with
    | none => true
    | some _ => false)

def unicodeStringLiteralFunction : FunctionDecl :=
  { name := some "unicodeLiteral"
    returns :=
      [ { name := some "text", ty := Ty.string }
      , { name := some "fixed", ty := Ty.bytesN 3 } ]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.tuple
              [ TupleItem.value
                  (Expr.literal (Literal.unicodeString "é"))
              , TupleItem.value
                  (Expr.call (Expr.typeName (Ty.bytesN 3))
                    [Arg.positional
                      (Expr.literal (Literal.unicodeString "é"))]) ]))) }

def unicodeStringLiteralCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty unicodeStringLiteralFunction []

def unicodeStringLiteralMatchesUtf8 : Option Bool := do
  let result ← unicodeStringLiteralCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.bytes text
      , SolidCore.Solidity.Source.Value.word fixed ] =>
      some (text == [0xc3, 0xa9] &&
        fixedBytesWordBytes 3 fixed == [0xc3, 0xa9, 0])
  | _ => some false

def addressLiteralConversionFunction : FunctionDecl :=
  { name := some "addressLiteralConversions"
    returns :=
      [ { name := some "zero", ty := Ty.address false }
      , { name := some "fromInteger", ty := Ty.address false }
      , { name := some "fromUint160", ty := Ty.address false }
      , { name := some "fromBytes20", ty := Ty.address false }
      , { name := some "payableZero", ty := Ty.address true }
      , { name := some "fromVarDecl", ty := Ty.address false } ]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [ { name := some "saved", ty := some (Ty.address false) } ]
              (some
                (Expr.call (Expr.typeName (Ty.address false))
                  [Arg.positional
                    (Expr.literal (Literal.number "0xbeef"))]))
          , Stmt.returnValues
              (some
                (Expr.tuple
                  [ TupleItem.value
                      (Expr.call (Expr.typeName (Ty.address false))
                        [Arg.positional
                          (Expr.literal (Literal.number "0"))])
                  , TupleItem.value
                      (Expr.call (Expr.typeName (Ty.address false))
                        [Arg.positional
                          (Expr.literal (Literal.number "0xbeef"))])
                  , TupleItem.value
                      (Expr.call (Expr.typeName (Ty.address false))
                        [Arg.positional
                          (Expr.call (Expr.typeName (Ty.uint 160))
                            [Arg.positional
                              (Expr.literal (Literal.number "0xcafe"))])])
                  , TupleItem.value
                      (Expr.call (Expr.typeName (Ty.address false))
                        [Arg.positional
                          (Expr.call (Expr.typeName (Ty.bytesN 20))
                            [Arg.positional
                              (Expr.literal
                                (Literal.number
                                  "0x111122223333444455556666777788889999aaaa"))])])
                  , TupleItem.value
                      (Expr.payableConversion
                        (Expr.literal (Literal.number "0")))
                  , TupleItem.value (Expr.ident "saved") ])) ]) }

def addressLiteralConversionCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty
    addressLiteralConversionFunction []

def addressLiteralConversionMatchesExpected : Option Bool := do
  let result ← addressLiteralConversionCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word zeroValue
      , SolidCore.Solidity.Source.Value.word fromInteger
      , SolidCore.Solidity.Source.Value.word fromUint160
      , SolidCore.Solidity.Source.Value.word fromBytes20
      , SolidCore.Solidity.Source.Value.word payableZero
      , SolidCore.Solidity.Source.Value.word fromVarDecl ] =>
      some (zeroValue == 0 &&
        fromInteger == 0xbeef &&
        fromUint160 == 0xcafe &&
        fromBytes20 == 0x111122223333444455556666777788889999aaaa &&
        payableZero == 0 &&
        fromVarDecl == 0xbeef)
  | _ => some false

def addressConversionRejected : Bool :=
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.address false))
          [Arg.positional
            (Expr.literal
              (Literal.number
                "0x10000000000000000000000000000000000000000"))])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.address false))
          [Arg.positional
            (Expr.call (Expr.typeName (Ty.uint 256))
              [Arg.positional (Expr.literal (Literal.number "1"))])])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.address false))
          [Arg.positional
            (Expr.call (Expr.typeName (Ty.bytesN 32))
              [Arg.positional
                (Expr.literal
                  (Literal.number
                    "0x111122223333444455556666777788889999aaaabbbbccccddddeeeeffff0000"))])])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.call (Expr.typeName (Ty.address false))
          [Arg.positional (Expr.literal (Literal.string "x"))])
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.payableConversion (Expr.literal (Literal.number "1")))
    with
    | none => true
    | some _ => false) &&
  (match
      Expr.toCore? []
        (Expr.payableConversion
          (Expr.call (Expr.typeName (Ty.uint 160))
            [Arg.positional (Expr.literal (Literal.number "1"))]))
    with
    | none => true
    | some _ => false)

def hexStringLiteralFunction : FunctionDecl :=
  { name := some "hexData"
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.returnValues
          (some (Expr.literal (Literal.hexString "0011_22FF")))) }

def hexStringLiteralCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
    SolidCore.Solidity.Source.State.empty hexStringLiteralFunction []

def hexStringLiteralMatchesExpected : Option Bool := do
  let result ← hexStringLiteralCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      some (bytes == [0, 17, 34, 255])
  | _ => some false

def hexStringAbiEncodeFunction : FunctionDecl :=
  { name := some "encodeHexData"
    returns := [{ name := some "out", ty := Ty.bytes }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.member (Expr.ident "abi") "encode")
              [Arg.positional
                (Expr.literal (Literal.hexString "dead_beef"))]))) }

def hexStringAbiEncodeExpected : Option (List Byte) :=
  SolidCore.Solidity.Source.ABI.encodeValues?
    [SolidCore.Solidity.Source.Ty.bytesCalldata]
    [SolidCore.Solidity.Source.Value.bytes [0xde, 0xad, 0xbe, 0xef]]

def hexStringAbiEncodeMatchesExpected : Option Bool := do
  let result ←
    FunctionDecl.call? 8 [] [] SolidCore.Solidity.Source.Context.empty
      SolidCore.Solidity.Source.State.empty hexStringAbiEncodeFunction []
  let expected ← hexStringAbiEncodeExpected
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      some (bytes == expected)
  | _ => some false

def stringEchoFunction : FunctionDecl :=
  { name := some "echo"
    params := [{ name := some "message", ty := Ty.string }]
    returns := [{ name := some "out", ty := Ty.string }]
    body := some (Stmt.returnValues (some (Expr.ident "message"))) }

def stringEchoContract : ContractDecl :=
  { name := "Echo"
    items := [ContractItem.function stringEchoFunction] }

def stringEchoCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? stringEchoContract
  let function ← contract.findFunctionByName? "echo"
  let calldata ←
    SolidCore.Solidity.Source.ABI.calldataFor? function
      [SolidCore.Solidity.Source.Value.bytes
        ("ok".toList.map Char.toNat)]
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract SolidCore.Solidity.Source.State.empty calldata

def fallbackReceiveContract : ContractDecl :=
  { name := "FallbackReceive"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { kind := FunctionKind.fallback
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.literal (Literal.number "1")))) }
      , ContractItem.function
          { kind := FunctionKind.receive
            mutability := StateMutability.payable
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.literal (Literal.number "2")))) } ] }

def fallbackDispatchResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? fallbackReceiveContract
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract SolidCore.Solidity.Source.State.empty
    [0xde, 0xad, 0xbe, 0xef]

def receiveDispatchResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? fallbackReceiveContract
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract SolidCore.Solidity.Source.State.empty []

def fallbackBytesContract : ContractDecl :=
  { name := "FallbackBytes"
    items :=
      [ ContractItem.function
          { kind := FunctionKind.fallback
            params :=
              [{ name := some "input"
                 ty := Ty.bytes
                 location := some DataLocation.calldata }]
            returns :=
              [{ name := some "output"
                 ty := Ty.bytes
                 location := some DataLocation.memory }]
            body := some (Stmt.returnValues (some (Expr.ident "input"))) } ] }

def fallbackBytesDispatchResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? fallbackBytesContract
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract SolidCore.Solidity.Source.State.empty [1, 2, 3]

def fallbackMsgDataContract : ContractDecl :=
  { name := "FallbackMsgData"
    items :=
      [ ContractItem.function
          { kind := FunctionKind.fallback
            returns :=
              [{ name := some "output"
                 ty := Ty.bytes
                 location := some DataLocation.memory }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.member (Expr.ident "msg") "data"))) } ] }

def fallbackMsgDataDispatchResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? fallbackMsgDataContract
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract SolidCore.Solidity.Source.State.empty [4, 5, 6]

def receiveMsgValueContract : ContractDecl :=
  { name := "ReceiveValue"
    items :=
      [ ContractItem.stateVar { name := "last", ty := Ty.uint 256 }
      , ContractItem.function
          { kind := FunctionKind.receive
            mutability := StateMutability.payable
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "last") AssignOp.assign
                    (Expr.member (Expr.ident "msg") "value"))) } ] }

def receiveMsgValueDispatchResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? receiveMsgValueContract
  SolidCore.Solidity.Source.ABI.Contract.callCalldataFrom?
    16 contract SolidCore.Solidity.Source.State.empty
    0xabc 77 []

def fallbackMsgSenderContract : ContractDecl :=
  { name := "FallbackSender"
    items :=
      [ ContractItem.stateVar { name := "sender", ty := Ty.address false }
      , ContractItem.function
          { kind := FunctionKind.fallback
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "sender") AssignOp.assign
                    (Expr.member (Expr.ident "msg") "sender"))) } ] }

def fallbackMsgSenderDispatchResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? fallbackMsgSenderContract
  SolidCore.Solidity.Source.ABI.Contract.callCalldataFrom?
    16 contract SolidCore.Solidity.Source.State.empty
    0xabc 0 [0xff, 0xff, 0xff, 0xff]

def fallbackMsgSenderDispatchMatches : Option Bool := do
  let result ← fallbackMsgSenderDispatchResult
  some
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 0xabc &&
      result.output == [])

def payableFallbackValueContract : ContractDecl :=
  { name := "FallbackValue"
    items :=
      [ ContractItem.stateVar { name := "last", ty := Ty.uint 256 }
      , ContractItem.function
          { kind := FunctionKind.fallback
            mutability := StateMutability.payable
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "last") AssignOp.assign
                    (Expr.member (Expr.ident "msg") "value"))) } ] }

def payableFallbackValueDispatchResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? payableFallbackValueContract
  SolidCore.Solidity.Source.ABI.Contract.callCalldataFrom?
    16 contract SolidCore.Solidity.Source.State.empty
    0xabc 33 [0xff, 0xff, 0xff, 0xff]

def payableFallbackValueDispatchMatches : Option Bool := do
  let result ← payableFallbackValueDispatchResult
  some
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 33 &&
      result.output == [])

def payableFunctionValueContract : ContractDecl :=
  { name := "PayableValue"
    items :=
      [ ContractItem.stateVar { name := "last", ty := Ty.uint 256 }
      , ContractItem.function
          { name := some "deposit"
            mutability := StateMutability.payable
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "last") AssignOp.assign
                    (Expr.member (Expr.ident "msg") "value"))) } ] }

def payableFunctionValueDispatchResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? payableFunctionValueContract
  let function ← contract.findFunctionByName? "deposit"
  let calldata ←
    SolidCore.Solidity.Source.ABI.calldataFor? function []
  SolidCore.Solidity.Source.ABI.Contract.callCalldataFrom?
    16 contract SolidCore.Solidity.Source.State.empty
    0xabc 55 calldata

def payableFunctionValueDispatchMatches : Option Bool := do
  let result ← payableFunctionValueDispatchResult
  some
    (result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 55 &&
      result.output == [])

def nonpayableRejectsValueContract : ContractDecl :=
  { name := "NonpayableValue"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { name := some "touch"
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.literal (Literal.number "9")))) } ] }

def nonpayableRejectsValueDispatchResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let contract ← ContractDecl.toCore? nonpayableRejectsValueContract
  let function ← contract.findFunctionByName? "touch"
  let calldata ←
    SolidCore.Solidity.Source.ABI.calldataFor? function []
  SolidCore.Solidity.Source.ABI.Contract.callCalldataFrom?
    16 contract SolidCore.Solidity.Source.State.empty
    0xabc 1 calldata

def nonpayableRejectsValueDispatchMatches : Option Bool := do
  let result ← nonpayableRejectsValueDispatchResult
  some
    (!result.success &&
      SolidCore.Solidity.Source.wordEq (result.state.loadSlot 0) 0 &&
      result.output == [])

def directPayableFunction : FunctionDecl :=
  { name := some "paid"
    mutability := StateMutability.payable
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.returnValues
          (some (Expr.member (Expr.ident "msg") "value"))) }

def directPayableContext : CoreContext :=
  { SolidCore.Solidity.Source.Context.empty with value := 9 }

def directPayableCallResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] directPayableContext
    SolidCore.Solidity.Source.State.empty directPayableFunction []

def directPayableCallMatches : Option Bool := do
  let result ← directPayableCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 9)
  | _ => some false

def directNonpayableRejectResult : Option CoreCallResult :=
  FunctionDecl.call? 8 [] [] directPayableContext
    SolidCore.Solidity.Source.State.empty
    { directPayableFunction with
      mutability := StateMutability.nonpayable } []

def directNonpayableRejectMatches : Option Bool := do
  let result ← directNonpayableRejectResult
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state
      SolidCore.Solidity.Source.RevertData.empty =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0)
  | _ => some false

def payableConstructorValueContract : ContractDecl :=
  { name := "PayableCtor"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { kind := FunctionKind.constructor
            mutability := StateMutability.payable
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.member (Expr.ident "msg") "value"))) } ] }

def payableConstructorValueResult : Option CoreCallResult :=
  ContractDecl.constructFrom? 16 payableConstructorValueContract
    SolidCore.Solidity.Source.State.empty 0xabcd 13 []

def payableConstructorValueMatches : Option Bool := do
  let result ← payableConstructorValueResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 13)
  | _ => some false

def nonpayableConstructorRejectsValueResult : Option CoreCallResult :=
  ContractDecl.constructFrom? 16
    { payableConstructorValueContract with
      name := "NonpayableCtor"
      items :=
        [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
        , ContractItem.function
            { kind := FunctionKind.constructor
              mutability := StateMutability.nonpayable
              body :=
                some
                  (Stmt.expr
                    (Expr.assign (Expr.ident "x") AssignOp.assign
                      (Expr.literal (Literal.number "17")))) } ] }
    SolidCore.Solidity.Source.State.empty 0xabcd 13 []

def nonpayableConstructorRejectsValueMatches : Option Bool := do
  let result ← nonpayableConstructorRejectsValueResult
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state
      SolidCore.Solidity.Source.RevertData.empty =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0)
  | _ => some false

def externalCalldata? (signature : String)
    (tys : List SolidCore.Solidity.Source.Ty)
    (values : List SolidCore.Solidity.Source.Value) : Option (List Byte) := do
  let encoded ← SolidCore.Solidity.Source.ABI.encodeValues? tys values
  some
    (SolidCore.Solidity.Source.ABI.encodeSelector
      (SolidCore.Solidity.Source.ABI.selectorFromSignature signature) ++
      encoded)

def externalErrorBytes? (reason : String) : Option (List Byte) := do
  let encoded ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.bytesCalldata]
      [SolidCore.Solidity.Source.Value.bytes
        (reason.toList.map Char.toNat)]
  some
    (SolidCore.Solidity.Source.ABI.encodeSelector
      SolidCore.Solidity.Source.ABI.errorSelector ++ encoded)

def externalPanicBytes? (code : Word) : Option (List Byte) := do
  let encoded ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word code]
  some
    (SolidCore.Solidity.Source.ABI.encodeSelector
      SolidCore.Solidity.Source.ABI.panicSelector ++ encoded)

def tryCatchSuccessFunction : FunctionDecl :=
  { name := some "read"
    params :=
      [ { name := some "target", ty := Ty.address false }
      , { name := some "key", ty := Ty.uint 256 } ]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.tryCatchReturns
          (Expr.call (Expr.member (Expr.ident "target") "get")
            [Arg.positional (Expr.ident "key")])
          [{ name := some "value", ty := Ty.uint 256 }]
          (Stmt.returnValues
            (some
              (Expr.binary BinaryOp.add
                (Expr.ident "value")
                (Expr.literal (Literal.number "1")))))
          [ CatchClause.clause none []
              (Stmt.returnValues
                (some (Expr.literal (Literal.number "0")))) ]) }

def tryCatchSuccessContext : Option CoreContext := do
  let callData ←
    externalCalldata? "get(uint256)"
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let output ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 41]
  some
    { SolidCore.Solidity.Source.Context.empty with
      lowLevelCallResults :=
        [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
            target := 0xbeef
            calldata := callData
            success := true
            output := output } ] }

def tryCatchSuccessResult : Option CoreCallResult := do
  let context ← tryCatchSuccessContext
  FunctionDecl.call? 16 [] [] context
    SolidCore.Solidity.Source.State.empty tryCatchSuccessFunction
    [ SolidCore.Solidity.Source.Value.word 0xbeef
    , SolidCore.Solidity.Source.Value.word 7 ]

def tryCatchSuccessMatches : Option Bool := do
  let result ← tryCatchSuccessResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 42)
  | _ => some false

def tryCatchErrorFunction : FunctionDecl :=
  { name := some "readError"
    params := [{ name := some "target", ty := Ty.address false }]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.tryCatchReturns
          (Expr.call (Expr.member (Expr.ident "target") "get") [])
          [{ name := some "value", ty := Ty.uint 256 }]
          (Stmt.returnValues (some (Expr.ident "value")))
          [ CatchClause.clause (some "Error")
              [{ name := some "reason"
                 ty := Ty.string
                 location := some DataLocation.memory }]
              (Stmt.returnValues
                (some
                  (Expr.member (Expr.ident "reason") "length")))
          , CatchClause.clause none []
              (Stmt.returnValues
                (some (Expr.literal (Literal.number "999")))) ]) }

def tryCatchErrorResult : Option CoreCallResult := do
  let callData ← externalCalldata? "get()" [] []
  let errorBytes ← externalErrorBytes? "bad"
  FunctionDecl.call? 16 [] []
    { SolidCore.Solidity.Source.Context.empty with
      lowLevelCallResults :=
        [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
            target := 0xbeef
            calldata := callData
            success := false
            output := errorBytes } ] }
    SolidCore.Solidity.Source.State.empty tryCatchErrorFunction
    [SolidCore.Solidity.Source.Value.word 0xbeef]

def tryCatchErrorMatches : Option Bool := do
  let result ← tryCatchErrorResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 3)
  | _ => some false

def tryCatchPanicFunction : FunctionDecl :=
  { name := some "readPanic"
    params := [{ name := some "target", ty := Ty.address false }]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.tryCatchReturns
          (Expr.call (Expr.member (Expr.ident "target") "get") [])
          [{ name := some "value", ty := Ty.uint 256 }]
          (Stmt.returnValues (some (Expr.ident "value")))
          [ CatchClause.clause (some "Panic")
              [{ name := some "code", ty := Ty.uint 256 }]
              (Stmt.returnValues (some (Expr.ident "code"))) ]) }

def tryCatchPanicResult : Option CoreCallResult := do
  let callData ← externalCalldata? "get()" [] []
  let panicBytes ← externalPanicBytes? 0x11
  FunctionDecl.call? 16 [] []
    { SolidCore.Solidity.Source.Context.empty with
      lowLevelCallResults :=
        [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
            target := 0xbeef
            calldata := callData
            success := false
            output := panicBytes } ] }
    SolidCore.Solidity.Source.State.empty tryCatchPanicFunction
    [SolidCore.Solidity.Source.Value.word 0xbeef]

def tryCatchPanicMatches : Option Bool := do
  let result ← tryCatchPanicResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 0x11)
  | _ => some false

def tryCatchLowLevelFunction : FunctionDecl :=
  { name := some "readRaw"
    params := [{ name := some "target", ty := Ty.address false }]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.tryCatchReturns
          (Expr.call (Expr.member (Expr.ident "target") "get") [])
          [{ name := some "value", ty := Ty.uint 256 }]
          (Stmt.returnValues (some (Expr.ident "value")))
          [ CatchClause.clause none
              [{ name := some "data"
                 ty := Ty.bytes
                 location := some DataLocation.memory }]
              (Stmt.returnValues
                (some (Expr.member (Expr.ident "data") "length"))) ]) }

def tryCatchLowLevelResult : Option CoreCallResult := do
  let callData ← externalCalldata? "get()" [] []
  FunctionDecl.call? 16 [] []
    { SolidCore.Solidity.Source.Context.empty with
      lowLevelCallResults :=
        [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
            target := 0xbeef
            calldata := callData
            success := false
            output := [0xaa, 0xbb, 0xcc] } ] }
    SolidCore.Solidity.Source.State.empty tryCatchLowLevelFunction
    [SolidCore.Solidity.Source.Value.word 0xbeef]

def tryCatchLowLevelMatches : Option Bool := do
  let result ← tryCatchLowLevelResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 3)
  | _ => some false

def tryCatchUnmatchedPropagatesRaw : Option Bool := do
  let callData ← externalCalldata? "get()" [] []
  let result ←
    FunctionDecl.call? 16 [] []
      { SolidCore.Solidity.Source.Context.empty with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := callData
              success := false
              output := [0xaa, 0xbb] } ] }
      SolidCore.Solidity.Source.State.empty
      { tryCatchPanicFunction with name := some "unmatched" }
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.raw bytes) =>
      some (bytes == [0xaa, 0xbb])
  | _ => some false

def highLevelExternalReturnFunction : FunctionDecl :=
  { name := some "readExternal"
    params := [{ name := some "target", ty := Ty.address false }]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.member (Expr.ident "target") "get") []))) }

def highLevelExternalReturnMatches : Option Bool := do
  let callData ← externalCalldata? "get()" [] []
  let output ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 77]
  let result ←
    FunctionDecl.call? 16 [] []
      { SolidCore.Solidity.Source.Context.empty with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := callData
              success := true
              output := output } ] }
      SolidCore.Solidity.Source.State.empty
      highLevelExternalReturnFunction
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 77)
  | _ => some false

def highLevelExternalVarDeclFunction : FunctionDecl :=
  { name := some "readViaLocal"
    params := [{ name := some "target", ty := Ty.address false }]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [{ name := some "value", ty := some (Ty.uint 256) }]
              (some
                (Expr.call (Expr.member (Expr.ident "target") "get") []))
          , Stmt.returnValues
              (some
                (Expr.binary BinaryOp.add
                  (Expr.ident "value")
                  (Expr.literal (Literal.number "1")))) ]) }

def highLevelExternalVarDeclMatches : Option Bool := do
  let callData ← externalCalldata? "get()" [] []
  let output ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 40]
  let result ←
    FunctionDecl.call? 16 [] []
      { SolidCore.Solidity.Source.Context.empty with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := callData
              success := true
              output := output } ] }
      SolidCore.Solidity.Source.State.empty
      highLevelExternalVarDeclFunction
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 41)
  | _ => some false

def highLevelExternalMultiVarDeclFunction : FunctionDecl :=
  { name := some "readPairViaLocals"
    params := [{ name := some "target", ty := Ty.address false }]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [ { name := some "left", ty := some (Ty.uint 256) }
              , { name := some "right", ty := some (Ty.uint 256) } ]
              (some
                (Expr.call (Expr.member (Expr.ident "target") "pair") []))
          , Stmt.returnValues
              (some
                (Expr.binary BinaryOp.add
                  (Expr.ident "left")
                  (Expr.ident "right"))) ]) }

def highLevelExternalMultiVarDeclMatches : Option Bool := do
  let callData ← externalCalldata? "pair()" [] []
  let output ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.uint256 ]
      [ SolidCore.Solidity.Source.Value.word 20
      , SolidCore.Solidity.Source.Value.word 22 ]
  let result ←
    FunctionDecl.call? 16 [] []
      { SolidCore.Solidity.Source.Context.empty with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := callData
              success := true
              output := output } ] }
      SolidCore.Solidity.Source.State.empty
      highLevelExternalMultiVarDeclFunction
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 42)
  | _ => some false

def highLevelExternalValueFunction : FunctionDecl :=
  { name := some "payExternal"
    params :=
      [ { name := some "target", ty := Ty.address false }
      , { name := some "amount", ty := Ty.uint 256 } ]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.callWithOptions
              (Expr.member (Expr.ident "target") "quote")
              [CallOption.named "value" (Expr.ident "amount")]
              []))) }

def highLevelExternalValueMatches : Option Bool := do
  let callData ← externalCalldata? "quote()" [] []
  let output ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 9]
  let result ←
    FunctionDecl.call? 16 [] []
      { SolidCore.Solidity.Source.Context.empty with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := callData
              value := 5
              success := true
              output := output } ] }
      SolidCore.Solidity.Source.State.empty
      highLevelExternalValueFunction
      [ SolidCore.Solidity.Source.Value.word 0xbeef
      , SolidCore.Solidity.Source.Value.word 5 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 9)
  | _ => some false

def highLevelExternalAssignContract : ContractDecl :=
  { name := "ExternalAssign"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { name := some "load"
            params := [{ name := some "target", ty := Ty.address false }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.call
                      (Expr.member (Expr.ident "target") "get")
                      []))) } ] }

def highLevelExternalAssignMatches : Option Bool := do
  let contract ← ContractDecl.toCore? highLevelExternalAssignContract
  let function ← contract.findFunctionByName? "load"
  let callData ← externalCalldata? "get()" [] []
  let output ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 12]
  let result ←
    SolidCore.Solidity.Source.FunctionDef.call? 16
      { contract.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := callData
              success := true
              output := output } ] }
      function SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 12)
  | _ => some false

def highLevelExternalDiscardFunction : FunctionDecl :=
  { name := some "notifyExternal"
    params := [{ name := some "target", ty := Ty.address false }]
    body :=
      some
        (Stmt.expr
          (Expr.call (Expr.member (Expr.ident "target") "notify") [])) }

def highLevelExternalDiscardMatches : Option Bool := do
  let callData ← externalCalldata? "notify()" [] []
  let result ←
    FunctionDecl.call? 16 [] []
      { SolidCore.Solidity.Source.Context.empty with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := callData
              success := true
              output := [] } ] }
      SolidCore.Solidity.Source.State.empty
      highLevelExternalDiscardFunction
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [] => some true
  | _ => some false

def highLevelExternalFailureBubblesRaw : Option Bool := do
  let callData ← externalCalldata? "get()" [] []
  let result ←
    FunctionDecl.call? 16 [] []
      { SolidCore.Solidity.Source.Context.empty with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := callData
              success := false
              output := [0xdd, 0xee] } ] }
      SolidCore.Solidity.Source.State.empty
      highLevelExternalReturnFunction
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.raw bytes) =>
      some (bytes == [0xdd, 0xee])
  | _ => some false

def sendValueFunction : FunctionDecl :=
  { name := some "sendValue"
    params :=
      [ { name := some "target", ty := Ty.address true }
      , { name := some "amount", ty := Ty.uint 256 } ]
    returns := [{ name := some "ok", ty := Ty.bool }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.call (Expr.member (Expr.ident "target") "send")
              [Arg.positional (Expr.ident "amount")]))) }

def sendValueMatches : Option Bool := do
  let result ←
    FunctionDecl.call? 16 [] []
      { SolidCore.Solidity.Source.Context.empty with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := []
              value := 5
              success := true
              output := [] } ] }
      SolidCore.Solidity.Source.State.empty
      sendValueFunction
      [ SolidCore.Solidity.Source.Value.word 0xbeef
      , SolidCore.Solidity.Source.Value.word 5 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word ok] =>
      some (SolidCore.Solidity.Source.wordEq ok 1)
  | _ => some false

def sendValueFailureReturnsFalse : Option Bool := do
  let result ←
    FunctionDecl.call? 16 [] []
      { SolidCore.Solidity.Source.Context.empty with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := []
              value := 5
              success := false
              output := [0xde, 0xad] } ] }
      SolidCore.Solidity.Source.State.empty
      sendValueFunction
      [ SolidCore.Solidity.Source.Value.word 0xbeef
      , SolidCore.Solidity.Source.Value.word 5 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word ok] =>
      some (SolidCore.Solidity.Source.wordEq ok 0)
  | _ => some false

def transferValueContract : ContractDecl :=
  { name := "TransferValue"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { name := some "pay"
            params :=
              [ { name := some "target", ty := Ty.address true }
              , { name := some "amount", ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign (Expr.ident "x") AssignOp.assign
                        (Expr.literal (Literal.number "1")))
                  , Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "target") "transfer")
                        [Arg.positional (Expr.ident "amount")])
                  , Stmt.expr
                      (Expr.assign (Expr.ident "x") AssignOp.assign
                        (Expr.literal (Literal.number "2"))) ]) } ] }

def transferValueSuccessMatches : Option Bool := do
  let contract ← ContractDecl.toCore? transferValueContract
  let function ← contract.findFunctionByName? "pay"
  let result ←
    SolidCore.Solidity.Source.FunctionDef.call? 16
      { contract.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := []
              value := 5
              success := true
              output := [] } ] }
      function SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 0xbeef
      , SolidCore.Solidity.Source.Value.word 5 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 2)
  | _ => some false

def transferValueFailureReverts : Option Bool := do
  let contract ← ContractDecl.toCore? transferValueContract
  let function ← contract.findFunctionByName? "pay"
  let result ←
    SolidCore.Solidity.Source.FunctionDef.call? 16
      { contract.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := []
              value := 5
              success := false
              output := [0xba, 0xad] } ] }
      function SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 0xbeef
      , SolidCore.Solidity.Source.Value.word 5 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state
      (SolidCore.Solidity.Source.RevertData.raw bytes) =>
      some
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0 &&
          bytes == [0xba, 0xad])
  | _ => some false

def createdChildTy : Ty :=
  Ty.user { segments := ["Child"] }

def contractCreationFunction : FunctionDecl :=
  { name := some "make"
    returns := [{ name := some "created", ty := createdChildTy }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.newExpr createdChildTy
              [Arg.positional (Expr.literal (Literal.number "7"))]))) }

def contractCreationSuccessMatches : Option Bool := do
  let constructorArgs ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let result ←
    FunctionDecl.call? 16 [] []
      { SolidCore.Solidity.Source.Context.empty with
        contractCreationResults :=
          [ { contractName := "Child"
              constructorArgs := constructorArgs
              success := true
              address := 0xc0de } ] }
      SolidCore.Solidity.Source.State.empty
      contractCreationFunction []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word address] =>
      some (SolidCore.Solidity.Source.wordEq address 0xc0de)
  | _ => some false

def contractCreationWithOptionsFunction : FunctionDecl :=
  { name := some "makeSalted"
    params :=
      [ { name := some "amount", ty := Ty.uint 256 }
      , { name := some "salt", ty := Ty.uint 256 } ]
    returns := [{ name := some "created", ty := createdChildTy }]
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.callWithOptions
              (Expr.newExpr createdChildTy [])
              [ CallOption.named "value" (Expr.ident "amount")
              , CallOption.named "salt" (Expr.ident "salt") ]
              [Arg.positional (Expr.literal (Literal.number "9"))]))) }

def contractCreationWithValueSaltMatches : Option Bool := do
  let constructorArgs ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 9]
  let result ←
    FunctionDecl.call? 16 [] []
      { SolidCore.Solidity.Source.Context.empty with
        contractCreationResults :=
          [ { contractName := "Child"
              constructorArgs := constructorArgs
              value := 5
              salt? := some 0x1234
              success := true
              address := 0xcafe } ] }
      SolidCore.Solidity.Source.State.empty
      contractCreationWithOptionsFunction
      [ SolidCore.Solidity.Source.Value.word 5
      , SolidCore.Solidity.Source.Value.word 0x1234 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word address] =>
      some (SolidCore.Solidity.Source.wordEq address 0xcafe)
  | _ => some false

def contractCreationFailureContract : ContractDecl :=
  { name := "CreateFailure"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { name := some "make"
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign (Expr.ident "x") AssignOp.assign
                        (Expr.literal (Literal.number "1")))
                  , Stmt.expr
                      (Expr.newExpr createdChildTy
                        [Arg.positional
                          (Expr.literal (Literal.number "7"))])
                  , Stmt.expr
                      (Expr.assign (Expr.ident "x") AssignOp.assign
                        (Expr.literal (Literal.number "2"))) ]) } ] }

def contractCreationFailureBubblesRaw : Option Bool := do
  let contract ← ContractDecl.toCore? contractCreationFailureContract
  let function ← contract.findFunctionByName? "make"
  let constructorArgs ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let result ←
    SolidCore.Solidity.Source.FunctionDef.call? 16
      { contract.context with
        contractCreationResults :=
          [ { contractName := "Child"
              constructorArgs := constructorArgs
              success := false
              output := [0xca, 0xfe] } ] }
      function SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted state
      (SolidCore.Solidity.Source.RevertData.raw bytes) =>
      some
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 0 &&
          bytes == [0xca, 0xfe])
  | _ => some false

def tryCatchCreationFunction : FunctionDecl :=
  { name := some "tryMake"
    returns := [{ name := some "created", ty := Ty.address false }]
    body :=
      some
        (Stmt.tryCatchReturns
          (Expr.newExpr createdChildTy
            [Arg.positional (Expr.literal (Literal.number "7"))])
          [{ name := some "child", ty := createdChildTy }]
          (Stmt.returnValues (some (Expr.ident "child")))
          [ CatchClause.clause none []
              (Stmt.returnValues
                (some (Expr.literal (Literal.address 0)))) ]) }

def tryCatchCreationSuccessMatches : Option Bool := do
  let constructorArgs ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let result ←
    FunctionDecl.call? 16 [] []
      { SolidCore.Solidity.Source.Context.empty with
        contractCreationResults :=
          [ { contractName := "Child"
              constructorArgs := constructorArgs
              success := true
              address := 0xc0de } ] }
      SolidCore.Solidity.Source.State.empty
      tryCatchCreationFunction []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word address] =>
      some (SolidCore.Solidity.Source.wordEq address 0xc0de)
  | _ => some false

def tryCatchCreationFailureMatches : Option Bool := do
  let constructorArgs ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let result ←
    FunctionDecl.call? 16 [] []
      { SolidCore.Solidity.Source.Context.empty with
        contractCreationResults :=
          [ { contractName := "Child"
              constructorArgs := constructorArgs
              success := false
              output := [0xca, 0xfe] } ] }
      SolidCore.Solidity.Source.State.empty
      tryCatchCreationFunction []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word address] =>
      some (SolidCore.Solidity.Source.wordEq address 0)
  | _ => some false

def transientStorageContract : ContractDecl :=
  { name := "TransientStorage"
    items :=
      [ ContractItem.stateVar
          { name := "persistent", ty := Ty.uint 256 }
      , ContractItem.stateVar
          { name := "scratch"
            ty := Ty.uint 256
            mutability := VarMutability.transient
            visibility := some Visibility.public_ }
      , ContractItem.function
          { name := some "setBoth"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign
                        (Expr.ident "persistent")
                        AssignOp.assign
                        (Expr.literal (Literal.number "7")))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.ident "scratch")
                        AssignOp.assign
                        (Expr.literal (Literal.number "9")))
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.ident "persistent")
                            (Expr.literal (Literal.number "10")))
                          (Expr.ident "scratch"))) ]) } ] }

def transientStorageIndependentSlotsMatches : Option Bool := do
  let result ←
    ContractDecl.call? 16 transientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "setBoth")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 79)
  | _ => some false

def transientPublicGetterMatches : Option Bool := do
  let writeResult ←
    ContractDecl.call? 16 transientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "setBoth")
      SolidCore.Solidity.Source.State.empty []
  let state ←
    match writeResult with
    | SolidCore.Solidity.Source.CallResult.returned state _ => some state
    | _ => none
  let result ←
    ContractDecl.call? 16 transientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "scratch")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 9)
  | _ => some false

def transientClearedAtTransactionBoundaryMatches : Option Bool := do
  let writeResult ←
    ContractDecl.callTransaction? 16 transientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "setBoth")
      SolidCore.Solidity.Source.State.empty []
  let state ←
    match writeResult with
    | SolidCore.Solidity.Source.CallResult.returned state
        [SolidCore.Solidity.Source.Value.word value] =>
        if SolidCore.Solidity.Source.wordEq value 79 then
          some state
        else
          none
    | _ => none
  let result ←
    ContractDecl.callTransaction? 16 transientStorageContract
      (SolidCore.Solidity.Source.CallTarget.name "scratch")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state'
      [SolidCore.Solidity.Source.Value.word value] =>
      some
        (SolidCore.Solidity.Source.wordEq value 0 &&
          state'.transient == [])
  | _ => some false

def mappingContract : ContractDecl :=
  { name := "Map"
    items :=
      [ ContractItem.stateVar
          { name := "m"
            ty := Ty.mapping (Ty.uint 256) (Ty.uint 256) }
      , ContractItem.function
          { name := some "set"
            body :=
              some
                (Stmt.expr
                  (Expr.assign
                    (Expr.index
                      (Expr.ident "m")
                      (Expr.literal (Literal.number "4")))
                    AssignOp.assign
                    (Expr.literal (Literal.number "9")))) }
      , ContractItem.function
          { name := some "get"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.index
                      (Expr.ident "m")
                      (Expr.literal (Literal.number "4"))))) } ] }

def mappingWriteResult : Option CoreCallResult :=
  ContractDecl.call? 16 mappingContract
    (SolidCore.Solidity.Source.CallTarget.name "set")
    SolidCore.Solidity.Source.State.empty []

def mappingReadAfterWriteResult : Option CoreCallResult := do
  let writeResult ← mappingWriteResult
  match writeResult with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      ContractDecl.call? 16 mappingContract
        (SolidCore.Solidity.Source.CallTarget.name "get")
        state []
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def publicMappingGetterContract : ContractDecl :=
  { name := "PublicMap"
    items :=
      [ ContractItem.stateVar
          { name := "m"
            ty := Ty.mapping (Ty.uint 256) (Ty.uint 256)
            visibility := some Visibility.public_ }
      , ContractItem.function
          { name := some "set"
            body :=
              some
                (Stmt.expr
                  (Expr.assign
                    (Expr.index
                      (Expr.ident "m")
                      (Expr.literal (Literal.number "4")))
                    AssignOp.assign
                    (Expr.literal (Literal.number "9")))) } ] }

def publicMappingGetterCallResult : Option CoreCallResult := do
  let writeResult ←
    ContractDecl.call? 16 publicMappingGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty []
  match writeResult with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      ContractDecl.call? 16 publicMappingGetterContract
        (SolidCore.Solidity.Source.CallTarget.name "m")
        state [SolidCore.Solidity.Source.Value.word 4]
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def publicMappingGetterCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let writeResult ←
    ContractDecl.call? 16 publicMappingGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty []
  let state ←
    match writeResult with
    | SolidCore.Solidity.Source.CallResult.returned state _ => some state
    | SolidCore.Solidity.Source.CallResult.reverted _ _ => none
  let contract ← ContractDecl.toCore? publicMappingGetterContract
  let function ← contract.findFunctionByName? "m"
  let calldata ←
    SolidCore.Solidity.Source.ABI.calldataFor? function
      [SolidCore.Solidity.Source.Value.word 4]
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract state calldata

def bytesStringMappingKeyContract : ContractDecl :=
  { name := "BytesStringMap"
    items :=
      [ ContractItem.stateVar
          { name := "mb"
            ty := Ty.mapping Ty.bytes (Ty.uint 256)
            visibility := some Visibility.public_ }
      , ContractItem.stateVar
          { name := "ms"
            ty := Ty.mapping Ty.string (Ty.uint 256)
            visibility := some Visibility.public_ }
      , ContractItem.function
          { name := some "setBytes"
            params :=
              [ { name := some "key"
                  ty := Ty.bytes
                  location := some DataLocation.calldata }
              , { name := some "value", ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.expr
                  (Expr.assign
                    (Expr.index (Expr.ident "mb") (Expr.ident "key"))
                    AssignOp.assign
                    (Expr.ident "value"))) }
      , ContractItem.function
          { name := some "setString"
            params :=
              [ { name := some "key"
                  ty := Ty.string
                  location := some DataLocation.calldata }
              , { name := some "value", ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.expr
                  (Expr.assign
                    (Expr.index (Expr.ident "ms") (Expr.ident "key"))
                    AssignOp.assign
                    (Expr.ident "value"))) }
      , ContractItem.function
          { name := some "readBytes"
            params :=
              [ { name := some "key"
                  ty := Ty.bytes
                  location := some DataLocation.calldata } ]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.index (Expr.ident "mb") (Expr.ident "key")))) }
      , ContractItem.function
          { name := some "readString"
            params :=
              [ { name := some "key"
                  ty := Ty.string
                  location := some DataLocation.calldata } ]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.index (Expr.ident "ms") (Expr.ident "key")))) } ] }

def bytesStringMappingWrittenState : Option CoreState := do
  let bytesSet ←
    ContractDecl.call? 24 bytesStringMappingKeyContract
      (SolidCore.Solidity.Source.CallTarget.name "setBytes")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.bytes [1, 2, 3]
      , SolidCore.Solidity.Source.Value.word 44 ]
  let state ←
    match bytesSet with
    | SolidCore.Solidity.Source.CallResult.returned state _ => some state
    | SolidCore.Solidity.Source.CallResult.reverted _ _ => none
  let stringSet ←
    ContractDecl.call? 24 bytesStringMappingKeyContract
      (SolidCore.Solidity.Source.CallTarget.name "setString")
      state
      [ SolidCore.Solidity.Source.Value.bytes ("hi".toList.map Char.toNat)
      , SolidCore.Solidity.Source.Value.word 55 ]
  match stringSet with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def bytesMappingKeyReadMatches : Option Bool := do
  let state ← bytesStringMappingWrittenState
  let result ←
    ContractDecl.call? 16 bytesStringMappingKeyContract
      (SolidCore.Solidity.Source.CallTarget.name "readBytes")
      state [SolidCore.Solidity.Source.Value.bytes [1, 2, 3]]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 44)
  | _ => some false

def bytesMappingDifferentKeyDefaultsToZero : Option Bool := do
  let state ← bytesStringMappingWrittenState
  let result ←
    ContractDecl.call? 16 bytesStringMappingKeyContract
      (SolidCore.Solidity.Source.CallTarget.name "readBytes")
      state [SolidCore.Solidity.Source.Value.bytes [1, 2, 4]]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 0)
  | _ => some false

def stringMappingKeyReadMatches : Option Bool := do
  let state ← bytesStringMappingWrittenState
  let result ←
    ContractDecl.call? 16 bytesStringMappingKeyContract
      (SolidCore.Solidity.Source.CallTarget.name "readString")
      state
      [SolidCore.Solidity.Source.Value.bytes ("hi".toList.map Char.toNat)]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 55)
  | _ => some false

def publicBytesMappingGetterCallMatches : Option Bool := do
  let state ← bytesStringMappingWrittenState
  let result ←
    ContractDecl.call? 16 bytesStringMappingKeyContract
      (SolidCore.Solidity.Source.CallTarget.name "mb")
      state [SolidCore.Solidity.Source.Value.bytes [1, 2, 3]]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 44)
  | _ => some false

def publicStringMappingGetterCalldataMatches : Option Bool := do
  let state ← bytesStringMappingWrittenState
  let contract ← ContractDecl.toCore? bytesStringMappingKeyContract
  let function ← contract.findFunctionByName? "ms"
  let calldata ←
    SolidCore.Solidity.Source.ABI.calldataFor? function
      [SolidCore.Solidity.Source.Value.bytes ("hi".toList.map Char.toNat)]
  let result ←
    SolidCore.Solidity.Source.ABI.Contract.callCalldata?
      16 contract state calldata
  let expected ←
    SolidCore.Solidity.Source.abiEncodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 55]
  some (result.success && result.output == expected)

def publicArrayGetterContract : ContractDecl :=
  { name := "PublicArray"
    items :=
      [ ContractItem.stateVar
          { name := "items"
            ty := Ty.array (Ty.uint 256) none
            visibility := some Visibility.public_ }
      , ContractItem.stateVar
          { name := "fixedItems"
            ty := Ty.array (Ty.uint 256) (some 3)
            visibility := some Visibility.public_ }
      , ContractItem.function
          { name := some "set"
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "0"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "0"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "7"))])
                  , Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "fixedItems")
                          (Expr.literal (Literal.number "1")))
                        AssignOp.assign
                        (Expr.literal (Literal.number "8"))) ]) } ] }

def publicArrayGetterWrittenState : Option CoreState := do
  let writeResult ←
    ContractDecl.call? 16 publicArrayGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty []
  match writeResult with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def publicDynamicArrayGetterCallResult : Option CoreCallResult := do
  let state ← publicArrayGetterWrittenState
  ContractDecl.call? 16 publicArrayGetterContract
    (SolidCore.Solidity.Source.CallTarget.name "items")
    state [SolidCore.Solidity.Source.Value.word 2]

def publicFixedArrayGetterCallResult : Option CoreCallResult := do
  let state ← publicArrayGetterWrittenState
  ContractDecl.call? 16 publicArrayGetterContract
    (SolidCore.Solidity.Source.CallTarget.name "fixedItems")
    state [SolidCore.Solidity.Source.Value.word 1]

def publicDynamicArrayGetterCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let state ← publicArrayGetterWrittenState
  let contract ← ContractDecl.toCore? publicArrayGetterContract
  let function ← contract.findFunctionByName? "items"
  let calldata ←
    SolidCore.Solidity.Source.ABI.calldataFor? function
      [SolidCore.Solidity.Source.Value.word 2]
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract state calldata

def publicFixedArrayGetterCalldataResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let state ← publicArrayGetterWrittenState
  let contract ← ContractDecl.toCore? publicArrayGetterContract
  let function ← contract.findFunctionByName? "fixedItems"
  let calldata ←
    SolidCore.Solidity.Source.ABI.calldataFor? function
      [SolidCore.Solidity.Source.Value.word 1]
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract state calldata

def publicDynamicArrayGetterOutOfBoundsResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let state ← publicArrayGetterWrittenState
  let contract ← ContractDecl.toCore? publicArrayGetterContract
  let function ← contract.findFunctionByName? "items"
  let calldata ←
    SolidCore.Solidity.Source.ABI.calldataFor? function
      [SolidCore.Solidity.Source.Value.word 3]
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract state calldata

def publicFixedArrayGetterOutOfBoundsResult :
    Option SolidCore.Solidity.Source.ABI.AbiCallResult := do
  let state ← publicArrayGetterWrittenState
  let contract ← ContractDecl.toCore? publicArrayGetterContract
  let function ← contract.findFunctionByName? "fixedItems"
  let calldata ←
    SolidCore.Solidity.Source.ABI.calldataFor? function
      [SolidCore.Solidity.Source.Value.word 3]
  SolidCore.Solidity.Source.ABI.Contract.callCalldata?
    16 contract state calldata

def dynamicStorageArrayContract : ContractDecl :=
  { name := "StorageArray"
    items :=
      [ ContractItem.stateVar
          { name := "items"
            ty := Ty.array (Ty.uint 256) none
            visibility := some Visibility.public_ }
      , ContractItem.function
          { name := some "pushTwoPop"
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "7"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "9"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "pop") []) ]) }
      , ContractItem.function
          { name := some "pushAssign"
            returns :=
              [ { name := some "len", ty := Ty.uint 256 }
              , { name := some "first", ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign
                        (Expr.call
                          (Expr.member (Expr.ident "items") "push") [])
                        AssignOp.assign
                        (Expr.literal (Literal.number "42")))
                  , Stmt.returnValues
                      (some
                        (Expr.tuple
                          [ TupleItem.value
                              (Expr.member (Expr.ident "items") "length")
                          , TupleItem.value
                              (Expr.index (Expr.ident "items")
                                (Expr.literal (Literal.number "0"))) ])) ]) }
      , ContractItem.function
          { name := some "length"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.member (Expr.ident "items") "length"))) }
      , ContractItem.function
          { name := some "popEmpty"
            body :=
              some
                (Stmt.expr
                  (Expr.call
                    (Expr.member (Expr.ident "items") "pop") [])) } ] }

def dynamicStorageArrayPushPopResult : Option CoreCallResult :=
  ContractDecl.call? 32 dynamicStorageArrayContract
    (SolidCore.Solidity.Source.CallTarget.name "pushTwoPop")
    SolidCore.Solidity.Source.State.empty []

def dynamicStorageArrayLengthAfterPushPop : Option CoreCallResult := do
  let result ← dynamicStorageArrayPushPopResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      ContractDecl.call? 16 dynamicStorageArrayContract
        (SolidCore.Solidity.Source.CallTarget.name "length")
        state []
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def dynamicStorageArrayGetterAfterPushPop : Option CoreCallResult := do
  let result ← dynamicStorageArrayPushPopResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      ContractDecl.call? 16 dynamicStorageArrayContract
        (SolidCore.Solidity.Source.CallTarget.name "items")
        state [SolidCore.Solidity.Source.Value.word 0]
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def dynamicStorageArrayPopEmptyResult : Option CoreCallResult :=
  ContractDecl.call? 16 dynamicStorageArrayContract
    (SolidCore.Solidity.Source.CallTarget.name "popEmpty")
    SolidCore.Solidity.Source.State.empty []

def dynamicStorageArrayPushAssignMatches : Option Bool := do
  let result ←
    ContractDecl.call? 32 dynamicStorageArrayContract
      (SolidCore.Solidity.Source.CallTarget.name "pushAssign")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word len
      , SolidCore.Solidity.Source.Value.word first ] =>
      some
        (SolidCore.Solidity.Source.wordEq len 1 &&
          SolidCore.Solidity.Source.wordEq first 42)
  | _ => some false

def storageDeleteContract : ContractDecl :=
  { name := "StorageDelete"
    items :=
      [ ContractItem.stateVar
          { name := "items"
            ty := Ty.array (Ty.uint 256) none }
      , ContractItem.stateVar
          { name := "fixedItems"
            ty := Ty.array (Ty.uint 256) (some 3) }
      , ContractItem.stateVar
          { name := "m"
            ty := Ty.mapping (Ty.uint 256) (Ty.uint 256) }
      , ContractItem.function
          { name := some "set"
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "7"))])
                  , Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "fixedItems")
                          (Expr.literal (Literal.number "1")))
                        AssignOp.assign
                        (Expr.literal (Literal.number "8")))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "m")
                          (Expr.literal (Literal.number "4")))
                        AssignOp.assign
                        (Expr.literal (Literal.number "9"))) ]) }
      , ContractItem.function
          { name := some "deleteDynamic"
            body :=
              some
                (Stmt.expr
                  (Expr.unary UnaryOp.delete (Expr.ident "items"))) }
      , ContractItem.function
          { name := some "deleteFixed"
            body :=
              some
                (Stmt.expr
                  (Expr.unary UnaryOp.delete (Expr.ident "fixedItems"))) }
      , ContractItem.function
          { name := some "deleteMapping"
            body :=
              some
                (Stmt.expr
                  (Expr.unary UnaryOp.delete (Expr.ident "m"))) }
      , ContractItem.function
          { name := some "deleteMappingKey"
            body :=
              some
                (Stmt.expr
                  (Expr.unary UnaryOp.delete
                    (Expr.index
                      (Expr.ident "m")
                      (Expr.literal (Literal.number "4"))))) }
      , ContractItem.function
          { name := some "length"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.member (Expr.ident "items") "length"))) }
      , ContractItem.function
          { name := some "readItem"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.index
                      (Expr.ident "items")
                      (Expr.literal (Literal.number "0"))))) }
      , ContractItem.function
          { name := some "readFixed"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.index
                      (Expr.ident "fixedItems")
                      (Expr.literal (Literal.number "1"))))) }
      , ContractItem.function
          { name := some "readMap"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.index
                      (Expr.ident "m")
                      (Expr.literal (Literal.number "4"))))) } ] }

def storageDeleteWrittenState : Option CoreState := do
  let result ←
    ContractDecl.call? 48 storageDeleteContract
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageDeleteDynamicState : Option CoreState := do
  let state ← storageDeleteWrittenState
  let result ←
    ContractDecl.call? 24 storageDeleteContract
      (SolidCore.Solidity.Source.CallTarget.name "deleteDynamic")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageDeleteDynamicLengthResult : Option CoreCallResult := do
  let state ← storageDeleteDynamicState
  ContractDecl.call? 16 storageDeleteContract
    (SolidCore.Solidity.Source.CallTarget.name "length")
    state []

def storageDeleteDynamicLengthZero : Option Bool := do
  let result ← storageDeleteDynamicLengthResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 0)
  | _ => some false

def storageDeleteDynamicIndexResult : Option CoreCallResult := do
  let state ← storageDeleteDynamicState
  ContractDecl.call? 16 storageDeleteContract
    (SolidCore.Solidity.Source.CallTarget.name "readItem")
    state []

def storageDeleteDynamicIndexReverts : Option Bool := do
  let result ← storageDeleteDynamicIndexResult
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      some (code == 0x32)
  | _ => some false

def storageDeleteFixedState : Option CoreState := do
  let state ← storageDeleteWrittenState
  let result ←
    ContractDecl.call? 24 storageDeleteContract
      (SolidCore.Solidity.Source.CallTarget.name "deleteFixed")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageDeleteFixedClearsElement : Option Bool := do
  let state ← storageDeleteFixedState
  let result ←
    ContractDecl.call? 16 storageDeleteContract
      (SolidCore.Solidity.Source.CallTarget.name "readFixed")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 0)
  | _ => some false

def storageDeleteMappingState : Option CoreState := do
  let state ← storageDeleteWrittenState
  let result ←
    ContractDecl.call? 24 storageDeleteContract
      (SolidCore.Solidity.Source.CallTarget.name "deleteMapping")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageDeleteMappingKeepsEntry : Option Bool := do
  let state ← storageDeleteMappingState
  let result ←
    ContractDecl.call? 16 storageDeleteContract
      (SolidCore.Solidity.Source.CallTarget.name "readMap")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 9)
  | _ => some false

def storageDeleteMappingKeyState : Option CoreState := do
  let state ← storageDeleteWrittenState
  let result ←
    ContractDecl.call? 24 storageDeleteContract
      (SolidCore.Solidity.Source.CallTarget.name "deleteMappingKey")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageDeleteMappingKeyClearsEntry : Option Bool := do
  let state ← storageDeleteMappingKeyState
  let result ←
    ContractDecl.call? 16 storageDeleteContract
      (SolidCore.Solidity.Source.CallTarget.name "readMap")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 0)
  | _ => some false

def storageArrayCopyContract : ContractDecl :=
  { name := "StorageArrayCopy"
    items :=
      [ ContractItem.stateVar
          { name := "items"
            ty := Ty.array (Ty.uint 256) none }
      , ContractItem.stateVar
          { name := "fixedItems"
            ty := Ty.array (Ty.uint 256) (some 3) }
      , ContractItem.function
          { name := some "copy"
            params :=
              [ { name := some "xs"
                  ty := Ty.array (Ty.uint 256) none
                  location := some DataLocation.calldata }
              , { name := some "ys"
                  ty := Ty.array (Ty.uint 256) (some 3)
                  location := some DataLocation.calldata } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign
                        (Expr.ident "items")
                        AssignOp.assign
                        (Expr.ident "xs"))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.ident "fixedItems")
                        AssignOp.assign
                        (Expr.ident "ys")) ]) }
      , ContractItem.function
          { name := some "length"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.member (Expr.ident "items") "length"))) }
      , ContractItem.function
          { name := some "readItem"
            params := [{ name := some "i", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.index
                      (Expr.ident "items")
                      (Expr.ident "i")))) }
      , ContractItem.function
          { name := some "readFixed"
            params := [{ name := some "i", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.index
                      (Expr.ident "fixedItems")
                      (Expr.ident "i")))) } ] }

def storageArrayCopyState : Option CoreState := do
  let result ←
    ContractDecl.call? 48 storageArrayCopyContract
      (SolidCore.Solidity.Source.CallTarget.name "copy")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.dynamicArray
          [ SolidCore.Solidity.Source.Value.word 5
          , SolidCore.Solidity.Source.Value.word 6 ]
      , SolidCore.Solidity.Source.Value.fixedArray
          [ SolidCore.Solidity.Source.Value.word 1
          , SolidCore.Solidity.Source.Value.word 2
          , SolidCore.Solidity.Source.Value.word 3 ] ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageArrayCopyLengthMatches : Option Bool := do
  let state ← storageArrayCopyState
  let result ←
    ContractDecl.call? 16 storageArrayCopyContract
      (SolidCore.Solidity.Source.CallTarget.name "length")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 2)
  | _ => some false

def storageArrayCopyDynamicElementMatches : Option Bool := do
  let state ← storageArrayCopyState
  let result ←
    ContractDecl.call? 16 storageArrayCopyContract
      (SolidCore.Solidity.Source.CallTarget.name "readItem")
      state [SolidCore.Solidity.Source.Value.word 1]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 6)
  | _ => some false

def storageArrayCopyFixedElementMatches : Option Bool := do
  let state ← storageArrayCopyState
  let result ←
    ContractDecl.call? 16 storageArrayCopyContract
      (SolidCore.Solidity.Source.CallTarget.name "readFixed")
      state [SolidCore.Solidity.Source.Value.word 2]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 3)
  | _ => some false

def storageArrayCopyRejectsWrongFixedSize : Option Bool := do
  match
    ContractDecl.call? 48 storageArrayCopyContract
      (SolidCore.Solidity.Source.CallTarget.name "copy")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.dynamicArray
          [SolidCore.Solidity.Source.Value.word 5]
      , SolidCore.Solidity.Source.Value.fixedArray
          [ SolidCore.Solidity.Source.Value.word 1
          , SolidCore.Solidity.Source.Value.word 2 ] ]
  with
  | none =>
      some true
  | some _ => some false

def storageReferenceAliasContract : ContractDecl :=
  { name := "StorageReferenceAlias"
    items :=
      [ ContractItem.stateVar
          { name := "items"
            ty := Ty.array (Ty.uint 256) none }
      , ContractItem.stateVar
          { name := "otherItems"
            ty := Ty.array (Ty.uint 256) none }
      , ContractItem.stateVar
          { name := "entries"
            ty := Ty.mapping (Ty.uint 256) (Ty.uint 256) }
      , ContractItem.function
          { name := some "aliasWrite"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "5"))])
                  , Stmt.varDecl
                      [ { name := some "ref"
                          ty := some (Ty.array (Ty.uint 256) none)
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "items"))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "ref")
                          (Expr.literal (Literal.number "0")))
                        AssignOp.assign
                        (Expr.literal (Literal.number "9")))
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.index
                              (Expr.ident "items")
                              (Expr.literal (Literal.number "0")))
                            (Expr.literal (Literal.number "10")))
                          (Expr.member (Expr.ident "ref") "length"))) ]) }
      , ContractItem.function
          { name := some "aliasMap"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "ref"
                          ty := some (Ty.mapping (Ty.uint 256) (Ty.uint 256))
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "entries"))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "ref")
                          (Expr.literal (Literal.number "4")))
                        AssignOp.assign
                        (Expr.literal (Literal.number "12")))
                  , Stmt.returnValues
                      (some
                        (Expr.index
                          (Expr.ident "entries")
                          (Expr.literal (Literal.number "4")))) ]) }
      , ContractItem.function
          { name := some "deleteAlias"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "ref"
                          ty := some (Ty.array (Ty.uint 256) none)
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "items"))
                  , Stmt.expr
                      (Expr.unary UnaryOp.delete (Expr.ident "ref"))
                  , Stmt.returnValues
                      (some (Expr.member (Expr.ident "items") "length")) ]) }
      , ContractItem.function
          { name := some "aliasPush"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "7"))])
                  , Stmt.varDecl
                      [ { name := some "ref"
                          ty := some (Ty.array (Ty.uint 256) none)
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "items"))
                  , Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "ref") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "6"))])
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.member (Expr.ident "items") "length")
                            (Expr.literal (Literal.number "10")))
                          (Expr.index
                            (Expr.ident "items")
                            (Expr.literal (Literal.number "1"))))) ]) }
      , ContractItem.function
          { name := some "aliasPushAssign"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "ref"
                          ty := some (Ty.array (Ty.uint 256) none)
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "items"))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.call
                          (Expr.member (Expr.ident "ref") "push") [])
                        AssignOp.assign
                        (Expr.literal (Literal.number "11")))
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.member (Expr.ident "items") "length")
                            (Expr.literal (Literal.number "10")))
                          (Expr.index
                            (Expr.ident "items")
                            (Expr.literal (Literal.number "0"))))) ]) }
      , ContractItem.function
          { name := some "aliasPop"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "7"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "6"))])
                  , Stmt.varDecl
                      [ { name := some "ref"
                          ty := some (Ty.array (Ty.uint 256) none)
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "items"))
                  , Stmt.expr
                      (Expr.call (Expr.member (Expr.ident "ref") "pop") [])
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.member (Expr.ident "items") "length")
                            (Expr.literal (Literal.number "10")))
                          (Expr.index
                            (Expr.ident "items")
                            (Expr.literal (Literal.number "0"))))) ]) }
      , ContractItem.function
          { name := some "aliasRebind"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "1"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "otherItems") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "2"))])
                  , Stmt.varDecl
                      [ { name := some "ref"
                          ty := some (Ty.array (Ty.uint 256) none)
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "items"))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.ident "ref")
                        AssignOp.assign
                        (Expr.ident "otherItems"))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "ref")
                          (Expr.literal (Literal.number "0")))
                        AssignOp.assign
                        (Expr.literal (Literal.number "9")))
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.index
                              (Expr.ident "items")
                              (Expr.literal (Literal.number "0")))
                            (Expr.literal (Literal.number "100")))
                          (Expr.index
                            (Expr.ident "otherItems")
                            (Expr.literal (Literal.number "0"))))) ]) }
      , ContractItem.function
          { name := some "aliasRebindFromAlias"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "3"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "otherItems") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "4"))])
                  , Stmt.varDecl
                      [ { name := some "ref"
                          ty := some (Ty.array (Ty.uint 256) none)
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "items"))
                  , Stmt.varDecl
                      [ { name := some "other"
                          ty := some (Ty.array (Ty.uint 256) none)
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "otherItems"))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.ident "ref")
                        AssignOp.assign
                        (Expr.ident "other"))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "ref")
                          (Expr.literal (Literal.number "0")))
                        AssignOp.assign
                        (Expr.literal (Literal.number "8")))
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.index
                              (Expr.ident "items")
                              (Expr.literal (Literal.number "0")))
                            (Expr.literal (Literal.number "100")))
                          (Expr.index
                            (Expr.ident "otherItems")
                            (Expr.literal (Literal.number "0"))))) ]) }
      , ContractItem.function
          { name := some "writeStorage"
            visibility := some Visibility.internal_
            params :=
              [ { name := some "xs"
                  ty := Ty.array (Ty.uint 256) none
                  location := some DataLocation.storage }
              , { name := some "value"
                  ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "xs")
                          (Expr.literal (Literal.number "0")))
                        AssignOp.assign
                        (Expr.ident "value")) ]) }
      , ContractItem.function
          { name := some "appendStorage"
            visibility := some Visibility.internal_
            params :=
              [ { name := some "xs"
                  ty := Ty.array (Ty.uint 256) none
                  location := some DataLocation.storage }
              , { name := some "value"
                  ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "xs") "push")
                        [Arg.positional (Expr.ident "value")]) ]) }
      , ContractItem.function
          { name := some "popStorage"
            visibility := some Visibility.internal_
            params :=
              [ { name := some "xs"
                  ty := Ty.array (Ty.uint 256) none
                  location := some DataLocation.storage } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call (Expr.member (Expr.ident "xs") "pop") []) ]) }
      , ContractItem.function
          { name := some "rebindStorage"
            visibility := some Visibility.internal_
            params :=
              [ { name := some "xs"
                  ty := Ty.array (Ty.uint 256) none
                  location := some DataLocation.storage }
              , { name := some "ys"
                  ty := Ty.array (Ty.uint 256) none
                  location := some DataLocation.storage }
              , { name := some "value"
                  ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign
                        (Expr.ident "xs")
                        AssignOp.assign
                        (Expr.ident "ys"))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "xs")
                          (Expr.literal (Literal.number "0")))
                        AssignOp.assign
                        (Expr.ident "value")) ]) }
      , ContractItem.function
          { name := some "rebindStorageToState"
            visibility := some Visibility.internal_
            params :=
              [ { name := some "xs"
                  ty := Ty.array (Ty.uint 256) none
                  location := some DataLocation.storage }
              , { name := some "value"
                  ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign
                        (Expr.ident "xs")
                        AssignOp.assign
                        (Expr.ident "otherItems"))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "xs")
                          (Expr.literal (Literal.number "0")))
                        AssignOp.assign
                        (Expr.ident "value")) ]) }
      , ContractItem.function
          { name := some "writeMappingStorage"
            visibility := some Visibility.internal_
            params :=
              [ { name := some "table"
                  ty := Ty.mapping (Ty.uint 256) (Ty.uint 256)
                  location := some DataLocation.storage }
              , { name := some "key"
                  ty := Ty.uint 256 }
              , { name := some "value"
                  ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "table")
                          (Expr.ident "key"))
                        AssignOp.assign
                        (Expr.ident "value")) ]) }
      , ContractItem.function
          { name := some "internalStorageParamWrite"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "1"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.ident "writeStorage")
                        [ Arg.positional (Expr.ident "items")
                        , Arg.positional
                            (Expr.literal (Literal.number "9")) ])
                  , Stmt.returnValues
                      (some
                        (Expr.index
                          (Expr.ident "items")
                          (Expr.literal (Literal.number "0")))) ]) }
      , ContractItem.function
          { name := some "internalStorageParamPush"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.ident "appendStorage")
                        [ Arg.positional (Expr.ident "items")
                        , Arg.positional
                            (Expr.literal (Literal.number "6")) ])
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.member (Expr.ident "items") "length")
                            (Expr.literal (Literal.number "10")))
                          (Expr.index
                            (Expr.ident "items")
                            (Expr.literal (Literal.number "0"))))) ]) }
      , ContractItem.function
          { name := some "internalStorageParamPop"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "4"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.ident "appendStorage")
                        [ Arg.positional (Expr.ident "items")
                        , Arg.positional
                            (Expr.literal (Literal.number "5")) ])
                  , Stmt.expr
                      (Expr.call
                        (Expr.ident "popStorage")
                        [Arg.positional (Expr.ident "items")])
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.member (Expr.ident "items") "length")
                            (Expr.literal (Literal.number "10")))
                          (Expr.index
                            (Expr.ident "items")
                            (Expr.literal (Literal.number "0"))))) ]) }
      , ContractItem.function
          { name := some "internalStorageParamAliasPush"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "ref"
                          ty := some (Ty.array (Ty.uint 256) none)
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "items"))
                  , Stmt.expr
                      (Expr.call
                        (Expr.ident "appendStorage")
                        [ Arg.positional (Expr.ident "ref")
                        , Arg.positional
                            (Expr.literal (Literal.number "7")) ])
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.member (Expr.ident "items") "length")
                            (Expr.literal (Literal.number "10")))
                          (Expr.index
                            (Expr.ident "items")
                            (Expr.literal (Literal.number "0"))))) ]) }
      , ContractItem.function
          { name := some "internalStorageParamRebind"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "2"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "otherItems") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "4"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.ident "rebindStorage")
                        [ Arg.positional (Expr.ident "items")
                        , Arg.positional (Expr.ident "otherItems")
                        , Arg.positional
                            (Expr.literal (Literal.number "11")) ])
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.index
                              (Expr.ident "items")
                              (Expr.literal (Literal.number "0")))
                            (Expr.literal (Literal.number "100")))
                          (Expr.index
                            (Expr.ident "otherItems")
                            (Expr.literal (Literal.number "0"))))) ]) }
      , ContractItem.function
          { name := some "internalStorageParamRebindToState"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "5"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "otherItems") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "6"))])
                  , Stmt.expr
                      (Expr.call
                        (Expr.ident "rebindStorageToState")
                        [ Arg.positional (Expr.ident "items")
                        , Arg.positional
                            (Expr.literal (Literal.number "12")) ])
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.index
                              (Expr.ident "items")
                              (Expr.literal (Literal.number "0")))
                            (Expr.literal (Literal.number "100")))
                          (Expr.index
                            (Expr.ident "otherItems")
                            (Expr.literal (Literal.number "0"))))) ]) }
      , ContractItem.function
          { name := some "internalStorageParamAliasArg"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "items") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "3"))])
                  , Stmt.varDecl
                      [ { name := some "ref"
                          ty := some (Ty.array (Ty.uint 256) none)
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "items"))
                  , Stmt.expr
                      (Expr.call
                        (Expr.ident "writeStorage")
                        [ Arg.positional (Expr.ident "ref")
                        , Arg.positional
                            (Expr.literal (Literal.number "8")) ])
                  , Stmt.returnValues
                      (some
                        (Expr.index
                          (Expr.ident "items")
                          (Expr.literal (Literal.number "0")))) ]) }
      , ContractItem.function
          { name := some "internalStorageMappingParamWrite"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.ident "writeMappingStorage")
                        [ Arg.positional (Expr.ident "entries")
                        , Arg.positional
                            (Expr.literal (Literal.number "5"))
                        , Arg.positional
                            (Expr.literal (Literal.number "23")) ])
                  , Stmt.returnValues
                      (some
                        (Expr.index
                          (Expr.ident "entries")
                          (Expr.literal (Literal.number "5")))) ]) }
      , ContractItem.function
          { name := some "internalStorageMappingParamAliasArg"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "ref"
                          ty := some
                            (Ty.mapping (Ty.uint 256) (Ty.uint 256))
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "entries"))
                  , Stmt.expr
                      (Expr.call
                        (Expr.ident "writeMappingStorage")
                        [ Arg.positional (Expr.ident "ref")
                        , Arg.positional
                            (Expr.literal (Literal.number "6"))
                        , Arg.positional
                            (Expr.literal (Literal.number "31")) ])
                  , Stmt.returnValues
                      (some
                        (Expr.index
                          (Expr.ident "entries")
                          (Expr.literal (Literal.number "6")))) ]) } ] }

def storageReferenceAliasMatches : Option Bool := do
  let result ←
    ContractDecl.call? 48 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "aliasWrite")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 91)
  | _ => some false

def storageReferenceMappingAliasMatches : Option Bool := do
  let result ←
    ContractDecl.call? 48 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "aliasMap")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 12)
  | _ => some false

def storageReferenceDeleteAliasRejected : Option Bool := do
  let result ←
    ContractDecl.call? 48 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "deleteAlias")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      some (code == 0)
  | _ => some false

def storageReferenceArrayPushMatches : Option Bool := do
  let result ←
    ContractDecl.call? 64 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "aliasPush")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 26)
  | _ => some false

def storageReferenceArrayPushAssignMatches : Option Bool := do
  let result ←
    ContractDecl.call? 64 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "aliasPushAssign")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 21)
  | _ => some false

def storageReferenceArrayPopMatches : Option Bool := do
  let result ←
    ContractDecl.call? 64 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "aliasPop")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 17)
  | _ => some false

def storageReferenceRebindMatches : Option Bool := do
  let result ←
    ContractDecl.call? 80 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "aliasRebind")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 109)
  | _ => some false

def storageReferenceRebindFromAliasMatches : Option Bool := do
  let result ←
    ContractDecl.call? 96 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "aliasRebindFromAlias")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 308)
  | _ => some false

def storageInternalReferenceParamWriteMatches : Option Bool := do
  let result ←
    ContractDecl.call? 80 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "internalStorageParamWrite")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 9)
  | _ => some false

def storageInternalReferenceParamAliasArgMatches : Option Bool := do
  let result ←
    ContractDecl.call? 96 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "internalStorageParamAliasArg")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 8)
  | _ => some false

def storageInternalReferenceParamPushMatches : Option Bool := do
  let result ←
    ContractDecl.call? 96 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "internalStorageParamPush")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 16)
  | _ => some false

def storageInternalReferenceParamPopMatches : Option Bool := do
  let result ←
    ContractDecl.call? 128 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "internalStorageParamPop")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 14)
  | _ => some false

def storageInternalReferenceParamAliasPushMatches : Option Bool := do
  let result ←
    ContractDecl.call? 96 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "internalStorageParamAliasPush")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 17)
  | _ => some false

def storageInternalReferenceParamRebindMatches : Option Bool := do
  let result ←
    ContractDecl.call? 128 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name "internalStorageParamRebind")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 211)
  | _ => some false

def storageInternalReferenceParamRebindToStateMatches : Option Bool := do
  let result ←
    ContractDecl.call? 128 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name
        "internalStorageParamRebindToState")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 512)
  | _ => some false

def storageInternalMappingParamWriteMatches : Option Bool := do
  let result ←
    ContractDecl.call? 96 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name
        "internalStorageMappingParamWrite")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 23)
  | _ => some false

def storageInternalMappingParamAliasArgMatches : Option Bool := do
  let result ←
    ContractDecl.call? 96 storageReferenceAliasContract
      (SolidCore.Solidity.Source.CallTarget.name
        "internalStorageMappingParamAliasArg")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 31)
  | _ => some false

def storageBytesContract : ContractDecl :=
  { name := "StorageBytes"
    items :=
      [ ContractItem.stateVar
          { name := "blob"
            ty := Ty.bytes }
      , ContractItem.function
          { name := some "set"
            params :=
              [{ name := some "input"
                 ty := Ty.bytes
                 location := some DataLocation.calldata }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign
                    (Expr.ident "blob")
                    AssignOp.assign
                    (Expr.ident "input"))) }
      , ContractItem.function
          { name := some "writeSecond"
            body :=
              some
                (Stmt.expr
                  (Expr.assign
                    (Expr.index
                      (Expr.ident "blob")
                      (Expr.literal (Literal.number "1")))
                    AssignOp.assign
                    (Expr.literal (Literal.number "9")))) }
      , ContractItem.function
          { name := some "pushFour"
            body :=
              some
                (Stmt.expr
                  (Expr.call
                    (Expr.member (Expr.ident "blob") "push")
                    [Arg.positional (Expr.literal (Literal.number "4"))])) }
      , ContractItem.function
          { name := some "pushZero"
            body :=
              some
                (Stmt.expr
                  (Expr.call
                    (Expr.member (Expr.ident "blob") "push") [])) }
      , ContractItem.function
          { name := some "popOne"
            body :=
              some
                (Stmt.expr
                  (Expr.call
                    (Expr.member (Expr.ident "blob") "pop") [])) }
      , ContractItem.function
          { name := some "aliasWriteSecond"
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "ref"
                          ty := some Ty.bytes
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "blob"))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "ref")
                          (Expr.literal (Literal.number "1")))
                        AssignOp.assign
                        (Expr.literal (Literal.number "8"))) ]) }
      , ContractItem.function
          { name := some "aliasPushFive"
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "ref"
                          ty := some Ty.bytes
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "blob"))
                  , Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "ref") "push")
                        [Arg.positional
                          (Expr.literal (Literal.number "5"))]) ]) }
      , ContractItem.function
          { name := some "aliasPopOne"
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "ref"
                          ty := some Ty.bytes
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "blob"))
                  , Stmt.expr
                      (Expr.call (Expr.member (Expr.ident "ref") "pop") []) ]) }
      , ContractItem.function
          { name := some "writeBytesStorage"
            visibility := some Visibility.internal_
            params :=
              [ { name := some "buf"
                  ty := Ty.bytes
                  location := some DataLocation.storage }
              , { name := some "i"
                  ty := Ty.uint 256 }
              , { name := some "value"
                  ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign
                        (Expr.index
                          (Expr.ident "buf")
                          (Expr.ident "i"))
                        AssignOp.assign
                        (Expr.ident "value")) ]) }
      , ContractItem.function
          { name := some "pushBytesStorage"
            visibility := some Visibility.internal_
            params :=
              [ { name := some "buf"
                  ty := Ty.bytes
                  location := some DataLocation.storage }
              , { name := some "value"
                  ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.ident "buf") "push")
                        [Arg.positional (Expr.ident "value")]) ]) }
      , ContractItem.function
          { name := some "popBytesStorage"
            visibility := some Visibility.internal_
            params :=
              [ { name := some "buf"
                  ty := Ty.bytes
                  location := some DataLocation.storage } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call (Expr.member (Expr.ident "buf") "pop") []) ]) }
      , ContractItem.function
          { name := some "internalBytesParamWriteSecond"
            body :=
              some
                (Stmt.expr
                  (Expr.call
                    (Expr.ident "writeBytesStorage")
                    [ Arg.positional (Expr.ident "blob")
                    , Arg.positional (Expr.literal (Literal.number "1"))
                    , Arg.positional (Expr.literal (Literal.number "7")) ])) }
      , ContractItem.function
          { name := some "internalBytesParamAliasPushSix"
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "ref"
                          ty := some Ty.bytes
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "blob"))
                  , Stmt.expr
                      (Expr.call
                        (Expr.ident "pushBytesStorage")
                        [ Arg.positional (Expr.ident "ref")
                        , Arg.positional
                            (Expr.literal (Literal.number "6")) ]) ]) }
      , ContractItem.function
          { name := some "internalBytesParamPopOne"
            body :=
              some
                (Stmt.expr
                  (Expr.call
                    (Expr.ident "popBytesStorage")
                    [Arg.positional (Expr.ident "blob")])) }
      , ContractItem.function
          { name := some "clear"
            body :=
              some
                (Stmt.expr
                  (Expr.unary UnaryOp.delete (Expr.ident "blob"))) }
      , ContractItem.function
          { name := some "length"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.member (Expr.ident "blob") "length"))) }
      , ContractItem.function
          { name := some "at"
            params := [{ name := some "i", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.bytesN 1 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.index
                      (Expr.ident "blob")
                      (Expr.ident "i")))) } ] }

def storageBytesSetState : Option CoreState := do
  let result ←
    ContractDecl.call? 24 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.bytes [10, 20]]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageBytesLengthMatches : Option Bool := do
  let state ← storageBytesSetState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "length")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 2)
  | _ => some false

def storageBytesIndexMatches : Option Bool := do
  let state ← storageBytesSetState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "at")
      state [SolidCore.Solidity.Source.Value.word 1]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 20)
  | _ => some false

def storageBytesWriteState : Option CoreState := do
  let state ← storageBytesSetState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "writeSecond")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageBytesWriteSecondMatches : Option Bool := do
  let state ← storageBytesWriteState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "at")
      state [SolidCore.Solidity.Source.Value.word 1]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 9)
  | _ => some false

def storageBytesPushFourState : Option CoreState := do
  let state ← storageBytesSetState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "pushFour")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageBytesPushFourMatches : Option Bool := do
  let state ← storageBytesPushFourState
  let lengthResult ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "length")
      state []
  let valueResult ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "at")
      state [SolidCore.Solidity.Source.Value.word 2]
  match lengthResult, valueResult with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word length],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (length == 3 && value == 4)
  | _, _ => some false

def storageBytesPushZeroState : Option CoreState := do
  let state ← storageBytesSetState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "pushZero")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageBytesPushZeroMatches : Option Bool := do
  let state ← storageBytesPushZeroState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "at")
      state [SolidCore.Solidity.Source.Value.word 2]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 0)
  | _ => some false

def storageBytesPopState : Option CoreState := do
  let state ← storageBytesPushFourState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "popOne")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageBytesPopLengthMatches : Option Bool := do
  let state ← storageBytesPopState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "length")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 2)
  | _ => some false

def storageBytesAliasWriteState : Option CoreState := do
  let state ← storageBytesSetState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "aliasWriteSecond")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageBytesAliasWriteSecondMatches : Option Bool := do
  let state ← storageBytesAliasWriteState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "at")
      state [SolidCore.Solidity.Source.Value.word 1]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 8)
  | _ => some false

def storageBytesAliasPushState : Option CoreState := do
  let state ← storageBytesSetState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "aliasPushFive")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageBytesAliasPushMatches : Option Bool := do
  let state ← storageBytesAliasPushState
  let lengthResult ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "length")
      state []
  let valueResult ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "at")
      state [SolidCore.Solidity.Source.Value.word 2]
  match lengthResult, valueResult with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word length],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (length == 3 && value == 5)
  | _, _ => some false

def storageBytesAliasPopState : Option CoreState := do
  let state ← storageBytesSetState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "aliasPopOne")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageBytesAliasPopMatches : Option Bool := do
  let state ← storageBytesAliasPopState
  let lengthResult ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "length")
      state []
  let valueResult ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "at")
      state [SolidCore.Solidity.Source.Value.word 0]
  match lengthResult, valueResult with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word length],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (length == 1 && value == 10)
  | _, _ => some false

def storageBytesInternalParamWriteState : Option CoreState := do
  let state ← storageBytesSetState
  let result ←
    ContractDecl.call? 24 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name
        "internalBytesParamWriteSecond")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageBytesInternalParamWriteSecondMatches : Option Bool := do
  let state ← storageBytesInternalParamWriteState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "at")
      state [SolidCore.Solidity.Source.Value.word 1]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 7)
  | _ => some false

def storageBytesInternalParamAliasPushState : Option CoreState := do
  let state ← storageBytesSetState
  let result ←
    ContractDecl.call? 32 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name
        "internalBytesParamAliasPushSix")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageBytesInternalParamAliasPushMatches : Option Bool := do
  let state ← storageBytesInternalParamAliasPushState
  let lengthResult ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "length")
      state []
  let valueResult ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "at")
      state [SolidCore.Solidity.Source.Value.word 2]
  match lengthResult, valueResult with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word length],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (length == 3 && value == 6)
  | _, _ => some false

def storageBytesInternalParamPopState : Option CoreState := do
  let state ← storageBytesSetState
  let result ←
    ContractDecl.call? 24 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name
        "internalBytesParamPopOne")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageBytesInternalParamPopMatches : Option Bool := do
  let state ← storageBytesInternalParamPopState
  let lengthResult ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "length")
      state []
  let valueResult ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "at")
      state [SolidCore.Solidity.Source.Value.word 0]
  match lengthResult, valueResult with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word length],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (length == 1 && value == 10)
  | _, _ => some false

def storageBytesClearState : Option CoreState := do
  let state ← storageBytesSetState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "clear")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageBytesClearLengthZero : Option Bool := do
  let state ← storageBytesClearState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "length")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 0)
  | _ => some false

def storageBytesClearIndexReverts : Option Bool := do
  let state ← storageBytesClearState
  let result ←
    ContractDecl.call? 16 storageBytesContract
      (SolidCore.Solidity.Source.CallTarget.name "at")
      state [SolidCore.Solidity.Source.Value.word 0]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      some (code == 0x32)
  | _ => some false

def storageStringGetterContract : ContractDecl :=
  { name := "StorageStringGetter"
    items :=
      [ ContractItem.stateVar
          { name := "greeting"
            ty := Ty.string
            visibility := some Visibility.public_ }
      , ContractItem.stateVar
          { name := "raw"
            ty := Ty.bytes
            visibility := some Visibility.public_ }
      , ContractItem.function
          { name := some "setGreeting"
            params :=
              [{ name := some "input"
                 ty := Ty.string
                 location := some DataLocation.calldata }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign
                    (Expr.ident "greeting")
                    AssignOp.assign
                    (Expr.ident "input"))) }
      , ContractItem.function
          { name := some "clearGreeting"
            body :=
              some
                (Stmt.expr
                  (Expr.unary UnaryOp.delete (Expr.ident "greeting"))) }
      , ContractItem.function
          { name := some "setRaw"
            params :=
              [{ name := some "input"
                 ty := Ty.bytes
                 location := some DataLocation.calldata }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign
                    (Expr.ident "raw")
                    AssignOp.assign
                    (Expr.ident "input"))) } ] }

def storageStringGreetingBytes : List Byte :=
  "Hi".toList.map Char.toNat

def storageStringSetState : Option CoreState := do
  let result ←
    ContractDecl.call? 24 storageStringGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "setGreeting")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.bytes storageStringGreetingBytes]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageStringPublicGetterMatches : Option Bool := do
  let state ← storageStringSetState
  let result ←
    ContractDecl.call? 16 storageStringGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "greeting")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      some (bytes == storageStringGreetingBytes)
  | _ => some false

def storageStringPublicGetterCalldataMatches : Option Bool := do
  let state ← storageStringSetState
  let contract ← ContractDecl.toCore? storageStringGetterContract
  let function ← contract.findFunctionByName? "greeting"
  let calldata ← SolidCore.Solidity.Source.ABI.calldataFor? function []
  let result ←
    SolidCore.Solidity.Source.ABI.Contract.callCalldata?
      16 contract state calldata
  let expected ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.bytesCalldata]
      [SolidCore.Solidity.Source.Value.bytes storageStringGreetingBytes]
  some (result.success && result.output == expected)

def storageStringClearState : Option CoreState := do
  let state ← storageStringSetState
  let result ←
    ContractDecl.call? 16 storageStringGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "clearGreeting")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageStringClearGetterEmpty : Option Bool := do
  let state ← storageStringClearState
  let result ←
    ContractDecl.call? 16 storageStringGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "greeting")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      some bytes.isEmpty
  | _ => some false

def storageBytesPublicGetterMatches : Option Bool := do
  let result ←
    ContractDecl.call? 24 storageStringGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "setRaw")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.bytes [1, 2, 3]]
  let state ←
    match result with
    | SolidCore.Solidity.Source.CallResult.returned state _ => some state
    | SolidCore.Solidity.Source.CallResult.reverted _ _ => none
  let result ←
    ContractDecl.call? 16 storageStringGetterContract
      (SolidCore.Solidity.Source.CallTarget.name "raw")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.bytes bytes] =>
      some (bytes == [1, 2, 3])
  | _ => some false

def overloadedDispatchContract : ContractDecl :=
  { name := "OverloadedDispatch"
    items :=
      [ ContractItem.function
          { name := some "pick"
            params := [{ name := some "flag", ty := Ty.bool }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.literal (Literal.number "1")))) }
      , ContractItem.function
          { name := some "pick"
            params := [{ name := some "value", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.literal (Literal.number "2")))) }
      , ContractItem.function
          { name := some "pick"
            params := [{ name := some "payload", ty := Ty.bytes }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.literal (Literal.number "3")))) } ] }

def overloadedDirectBoolCallMatches : Option Bool := do
  let result ←
    ContractDecl.call? 16 overloadedDispatchContract
      (SolidCore.Solidity.Source.CallTarget.name "pick")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 1]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 1)
  | _ => some false

def overloadedDirectUintCallMatches : Option Bool := do
  let result ←
    ContractDecl.call? 16 overloadedDispatchContract
      (SolidCore.Solidity.Source.CallTarget.name "pick")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 7]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 2)
  | _ => some false

def overloadedDirectBytesCallMatches : Option Bool := do
  let result ←
    ContractDecl.call? 16 overloadedDispatchContract
      (SolidCore.Solidity.Source.CallTarget.name "pick")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.bytes [1, 2]]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 3)
  | _ => some false

def overloadedAbiUintCallMatches : Option Bool := do
  let contract ← ContractDecl.toCore? overloadedDispatchContract
  let selector :=
    SolidCore.Solidity.Source.ABI.selectorFromSignature "pick(uint256)"
  let calldata ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 7]
  let result ←
    SolidCore.Solidity.Source.ABI.Contract.callCalldata?
      16 contract SolidCore.Solidity.Source.State.empty
      (SolidCore.Solidity.Source.wordToBytesBE
        SolidCore.Solidity.Source.selectorBytes selector ++ calldata)
  let expected ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 2]
  some (result.success && result.output == expected)

def overloadedAbiBytesCallMatches : Option Bool := do
  let contract ← ContractDecl.toCore? overloadedDispatchContract
  let selector :=
    SolidCore.Solidity.Source.ABI.selectorFromSignature "pick(bytes)"
  let calldata ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.bytesCalldata]
      [SolidCore.Solidity.Source.Value.bytes [1, 2]]
  let result ←
    SolidCore.Solidity.Source.ABI.Contract.callCalldata?
      16 contract SolidCore.Solidity.Source.State.empty
      (SolidCore.Solidity.Source.wordToBytesBE
        SolidCore.Solidity.Source.selectorBytes selector ++ calldata)
  let expected ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 3]
  some (result.success && result.output == expected)

def internalOverloadedDispatchContract : ContractDecl :=
  { name := "InternalOverloadedDispatch"
    items :=
      [ ContractItem.function
          { name := some "pick"
            params := [{ name := some "flag", ty := Ty.bool }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.literal (Literal.number "1")))) }
      , ContractItem.function
          { name := some "pick"
            params := [{ name := some "value", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.literal (Literal.number "2")))) }
      , ContractItem.function
          { name := some "pick"
            params := [{ name := some "payload", ty := Ty.bytes }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.literal (Literal.number "3")))) }
      , ContractItem.function
          { name := some "run"
            returns :=
              [ { name := some "fromBool", ty := Ty.uint 256 }
              , { name := some "fromUint", ty := Ty.uint 256 }
              , { name := some "fromBytes", ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [{ name := some "a", ty := some (Ty.uint 256) }]
                      (some
                        (Expr.call (Expr.ident "pick")
                          [Arg.positional
                            (Expr.literal (Literal.bool true))]))
                  , Stmt.varDecl
                      [{ name := some "b", ty := some (Ty.uint 256) }]
                      (some
                        (Expr.call (Expr.ident "pick")
                          [Arg.positional
                            (Expr.literal (Literal.number "7"))]))
                  , Stmt.varDecl
                      [{ name := some "payload", ty := some Ty.bytes }]
                      (some (Expr.literal (Literal.bytes [1, 2])))
                  , Stmt.varDecl
                      [{ name := some "c", ty := some (Ty.uint 256) }]
                      (some
                        (Expr.call (Expr.ident "pick")
                          [Arg.positional (Expr.ident "payload")]))
                  , Stmt.returnValues
                      (some
                        (Expr.tuple
                          [ TupleItem.value (Expr.ident "a")
                          , TupleItem.value (Expr.ident "b")
                          , TupleItem.value (Expr.ident "c") ])) ]) } ] }

def internalOverloadedDispatchCallResult : Option CoreCallResult :=
  ContractDecl.call? 48 internalOverloadedDispatchContract
    (SolidCore.Solidity.Source.CallTarget.name "run")
    SolidCore.Solidity.Source.State.empty []

def internalOverloadedDispatchMatchesExpected : Option Bool := do
  let result ← internalOverloadedDispatchCallResult
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [ SolidCore.Solidity.Source.Value.word fromBool
      , SolidCore.Solidity.Source.Value.word fromUint
      , SolidCore.Solidity.Source.Value.word fromBytes ] =>
      some (fromBool == 1 && fromUint == 2 && fromBytes == 3)
  | _ => some false

def pricePath : Path := { segments := ["Price"] }

def priceTy : Ty := Ty.user pricePath

def priceTypeDecl : UserValueTypeDecl :=
  { name := "Price", underlying := Ty.uint 256 }

def udvtContract : ContractDecl :=
  { name := "UDVT"
    items :=
      [ ContractItem.stateVar
          { name := "last", ty := priceTy, visibility := some Visibility.public_ }
      , ContractItem.eventDecl
          { name := "Seen"
            params := [{ name := some "price", ty := priceTy, indexed := true }] }
      , ContractItem.errorDecl
          { name := "Bad", params := [{ name := some "price", ty := priceTy }] }
      , ContractItem.function
          { name := some "set"
            params := [{ name := some "raw", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "last") AssignOp.assign
                    (Expr.call
                      (Expr.member (Expr.typeName priceTy) "wrap")
                      [Arg.positional (Expr.ident "raw")]))) }
      , ContractItem.function
          { name := some "read"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call
                      (Expr.member (Expr.typeName priceTy) "unwrap")
                      [Arg.positional (Expr.ident "last")]))) }
      , ContractItem.function
          { name := some "roundtrip"
            params := [{ name := some "raw", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [{ name := some "wrapped", ty := some priceTy }]
                      (some
                        (Expr.call
                          (Expr.member (Expr.typeName priceTy) "wrap")
                          [Arg.positional (Expr.ident "raw")]))
                  , Stmt.returnValues
                      (some
                        (Expr.call
                          (Expr.member (Expr.typeName priceTy) "unwrap")
                          [Arg.positional (Expr.ident "wrapped")])) ]) }
      , ContractItem.function
          { name := some "echo"
            params := [{ name := some "value", ty := priceTy }]
            returns := [{ name := some "out", ty := priceTy }]
            body := some (Stmt.returnValues (some (Expr.ident "value"))) } ] }

def udvtSourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.freeUserValueType priceTypeDecl
      , SourceItem.contract udvtContract ] }

def udvtSetState : Option CoreState := do
  let result ←
    SourceUnit.callContract? 32 udvtSourceUnit "UDVT"
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 42]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def udvtReadMatches : Option Bool := do
  let state ← udvtSetState
  let result ←
    SourceUnit.callContract? 32 udvtSourceUnit "UDVT"
      (SolidCore.Solidity.Source.CallTarget.name "read")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 42)
  | _ => some false

def udvtPublicGetterMatches : Option Bool := do
  let state ← udvtSetState
  let result ←
    SourceUnit.callContract? 32 udvtSourceUnit "UDVT"
      (SolidCore.Solidity.Source.CallTarget.name "last")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 42)
  | _ => some false

def udvtRoundtripMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 udvtSourceUnit "UDVT"
      (SolidCore.Solidity.Source.CallTarget.name "roundtrip")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 77]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 77)
  | _ => some false

def udvtAbiSetState : Option CoreState := do
  let contract ← SourceUnit.toCoreContract? udvtSourceUnit "UDVT"
  let selector :=
    SolidCore.Solidity.Source.ABI.selectorFromSignature "set(uint256)"
  let calldata ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 42]
  let result ←
    SolidCore.Solidity.Source.ABI.Contract.callCalldata?
      32 contract SolidCore.Solidity.Source.State.empty
      (SolidCore.Solidity.Source.wordToBytesBE
        SolidCore.Solidity.Source.selectorBytes selector ++ calldata)
  if result.success then
    some result.state
  else
    none

def udvtAbiGetterMatches : Option Bool := do
  let contract ← SourceUnit.toCoreContract? udvtSourceUnit "UDVT"
  let state ← udvtAbiSetState
  let selector :=
    SolidCore.Solidity.Source.ABI.selectorFromSignature "last()"
  let result ←
    SolidCore.Solidity.Source.ABI.Contract.callCalldata?
      32 contract state
      (SolidCore.Solidity.Source.wordToBytesBE
        SolidCore.Solidity.Source.selectorBytes selector)
  let expected ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 42]
  some (result.success && result.output == expected)

def udvtAbiEchoMatches : Option Bool := do
  let contract ← SourceUnit.toCoreContract? udvtSourceUnit "UDVT"
  let selector :=
    SolidCore.Solidity.Source.ABI.selectorFromSignature "echo(uint256)"
  let calldata ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 55]
  let result ←
    SolidCore.Solidity.Source.ABI.Contract.callCalldata?
      32 contract SolidCore.Solidity.Source.State.empty
      (SolidCore.Solidity.Source.wordToBytesBE
        SolidCore.Solidity.Source.selectorBytes selector ++ calldata)
  let expected ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 55]
  some (result.success && result.output == expected)

def udvtEventTopicMatches : Option Bool := do
  let contract ← SourceUnit.toCoreContract? udvtSourceUnit "UDVT"
  let event ←
    contract.eventDecls.find? (fun event => event.name == "Seen")
  let field ← event.fields.head?
  let fieldIsUint256 :=
    match field.ty with
    | SolidCore.Solidity.Source.Ty.uint256 => true
    | _ => false
  some
    (event.topic? ==
      some (SolidCore.Solidity.Source.Keccak.digestWord "Seen(uint256)") &&
      fieldIsUint256 && field.indexed)

def udvtErrorSelectorMatches : Option Bool := do
  let contract ← SourceUnit.toCoreContract? udvtSourceUnit "UDVT"
  let err ←
    contract.errorDecls.find? (fun err => err.name == "Bad")
  let field ← err.fields.head?
  let fieldIsUint256 :=
    match field with
    | SolidCore.Solidity.Source.Ty.uint256 => true
    | _ => false
  some
    (err.selector ==
      SolidCore.Solidity.Source.ABI.selectorFromSignature "Bad(uint256)" &&
      fieldIsUint256)

def actionPath : Path := { segments := ["ActionChoices"] }

def actionTy : Ty := Ty.user actionPath

def actionEnumDecl : EnumDecl :=
  { name := "ActionChoices"
    cases := ["GoLeft", "GoRight", "GoStraight", "SitStill"] }

def enumContract : ContractDecl :=
  { name := "EnumDemo"
    items :=
      [ ContractItem.stateVar
          { name := "choice"
            ty := actionTy
            visibility := some Visibility.public_ }
      , ContractItem.eventDecl
          { name := "Seen"
            params := [{ name := some "choice", ty := actionTy, indexed := true }] }
      , ContractItem.errorDecl
          { name := "Bad"
            params := [{ name := some "choice", ty := actionTy }] }
      , ContractItem.function
          { name := some "setGoStraight"
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "choice") AssignOp.assign
                    (Expr.member (Expr.typeName actionTy) "GoStraight"))) }
      , ContractItem.function
          { name := some "setFromUint"
            params := [{ name := some "raw", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "choice") AssignOp.assign
                    (Expr.call (Expr.typeName actionTy)
                      [Arg.positional (Expr.ident "raw")]))) }
      , ContractItem.function
          { name := some "largest"
            returns := [{ name := some "out", ty := actionTy }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.member (Expr.typeName actionTy) "max"))) }
      , ContractItem.function
          { name := some "smallest"
            returns := [{ name := some "out", ty := actionTy }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.member (Expr.typeName actionTy) "min"))) }
      , ContractItem.function
          { name := some "readAsUint"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call (Expr.typeName (Ty.uint 256))
                      [Arg.positional (Expr.ident "choice")]))) }
      , ContractItem.function
          { name := some "echo"
            params := [{ name := some "value", ty := actionTy }]
            returns := [{ name := some "out", ty := actionTy }]
            body := some (Stmt.returnValues (some (Expr.ident "value"))) } ] }

def enumSourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.freeEnum actionEnumDecl
      , SourceItem.contract enumContract ] }

def enumSetState : Option CoreState := do
  let result ←
    SourceUnit.callContract? 32 enumSourceUnit "EnumDemo"
      (SolidCore.Solidity.Source.CallTarget.name "setGoStraight")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def enumPublicGetterMatches : Option Bool := do
  let state ← enumSetState
  let result ←
    SourceUnit.callContract? 32 enumSourceUnit "EnumDemo"
      (SolidCore.Solidity.Source.CallTarget.name "choice")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 2)
  | _ => some false

def enumReadAsUintMatches : Option Bool := do
  let state ← enumSetState
  let result ←
    SourceUnit.callContract? 32 enumSourceUnit "EnumDemo"
      (SolidCore.Solidity.Source.CallTarget.name "readAsUint")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 2)
  | _ => some false

def enumTypeMinMaxMatches : Option Bool := do
  let largest ←
    SourceUnit.callContract? 32 enumSourceUnit "EnumDemo"
      (SolidCore.Solidity.Source.CallTarget.name "largest")
      SolidCore.Solidity.Source.State.empty []
  let smallest ←
    SourceUnit.callContract? 32 enumSourceUnit "EnumDemo"
      (SolidCore.Solidity.Source.CallTarget.name "smallest")
      SolidCore.Solidity.Source.State.empty []
  match largest, smallest with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word maxValue],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word minValue] =>
      some (maxValue == 3 && minValue == 0)
  | _, _ => some false

def enumConversionInRangeMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 enumSourceUnit "EnumDemo"
      (SolidCore.Solidity.Source.CallTarget.name "setFromUint")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 1]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      let read ←
        SourceUnit.callContract? 32 enumSourceUnit "EnumDemo"
          (SolidCore.Solidity.Source.CallTarget.name "choice")
          state []
      match read with
      | SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word value] =>
          some (value == 1)
      | _ => some false
  | _ => some false

def enumConversionOutOfRangePanics : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 enumSourceUnit "EnumDemo"
      (SolidCore.Solidity.Source.CallTarget.name "setFromUint")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 9]
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      some (code == 0x21)
  | _ => some false

def enumAbiEchoUsesUint8Selector : Option Bool := do
  let contract ← SourceUnit.toCoreContract? enumSourceUnit "EnumDemo"
  let selector :=
    SolidCore.Solidity.Source.ABI.selectorFromSignature "echo(uint8)"
  let calldata ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 3]
  let result ←
    SolidCore.Solidity.Source.ABI.Contract.callCalldata?
      32 contract SolidCore.Solidity.Source.State.empty
      (SolidCore.Solidity.Source.wordToBytesBE
        SolidCore.Solidity.Source.selectorBytes selector ++ calldata)
  let expected ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 3]
  some (result.success && result.output == expected)

def enumEventTopicMatches : Option Bool := do
  let contract ← SourceUnit.toCoreContract? enumSourceUnit "EnumDemo"
  let event ←
    contract.eventDecls.find? (fun event => event.name == "Seen")
  let field ← event.fields.head?
  let fieldIsUint :=
    match field.ty with
    | SolidCore.Solidity.Source.Ty.uint256 => true
    | _ => false
  some
    (event.topic? ==
      some (SolidCore.Solidity.Source.Keccak.digestWord "Seen(uint8)") &&
      fieldIsUint && field.indexed)

def enumErrorSelectorMatches : Option Bool := do
  let contract ← SourceUnit.toCoreContract? enumSourceUnit "EnumDemo"
  let err ←
    contract.errorDecls.find? (fun err => err.name == "Bad")
  let field ← err.fields.head?
  let fieldIsUint :=
    match field with
    | SolidCore.Solidity.Source.Ty.uint256 => true
    | _ => false
  some
    (err.selector ==
      SolidCore.Solidity.Source.ABI.selectorFromSignature "Bad(uint8)" &&
      fieldIsUint)

def pointPath : Path := { segments := ["Point"] }

def pointTy : Ty := Ty.user pointPath

def pointStructDecl : StructDecl :=
  { name := "Point"
    fields :=
      [ { name := "x", ty := Ty.uint 256 }
      , { name := "y", ty := Ty.uint 256 } ] }

def pointConstructorNamed (x y : Expr) : Expr :=
  Expr.call (Expr.typeName pointTy)
    [ Arg.named "x" x
    , Arg.named "y" y ]

def pointConstructorPositional (x y : Expr) : Expr :=
  Expr.call (Expr.typeName pointTy)
    [ Arg.positional x
    , Arg.positional y ]

def structContract : ContractDecl :=
  { name := "StructDemo"
    items :=
      [ ContractItem.eventDecl
          { name := "Seen"
            params := [{ name := some "point", ty := pointTy, indexed := false }] }
      , ContractItem.errorDecl
          { name := "Bad"
            params := [{ name := some "point", ty := pointTy }] }
      , ContractItem.function
          { name := some "sum"
            params :=
              [ { name := some "x", ty := Ty.uint 256 }
              , { name := some "y", ty := Ty.uint 256 } ]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [{ name := some "point", ty := some pointTy }]
                      (some
                        (pointConstructorNamed
                          (Expr.ident "x") (Expr.ident "y")))
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.member (Expr.ident "point") "x")
                          (Expr.member (Expr.ident "point") "y"))) ]) }
      , ContractItem.function
          { name := some "replaceY"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [{ name := some "point", ty := some pointTy }]
                      (some
                        (pointConstructorPositional
                          (Expr.literal (Literal.number "1"))
                          (Expr.literal (Literal.number "2"))))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.member (Expr.ident "point") "y")
                        AssignOp.assign
                        (Expr.literal (Literal.number "9")))
                  , Stmt.returnValues
                      (some (Expr.member (Expr.ident "point") "y")) ]) }
      , ContractItem.function
          { name := some "echo"
            params := [{ name := some "point", ty := pointTy }]
            returns := [{ name := some "out", ty := pointTy }]
            body := some (Stmt.returnValues (some (Expr.ident "point"))) } ] }

def structSourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.freeStruct pointStructDecl
      , SourceItem.contract structContract ] }

def structNamedConstructorFieldSumMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 48 structSourceUnit "StructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "sum")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 7
      , SolidCore.Solidity.Source.Value.word 8 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 15)
  | _ => some false

def structFieldAssignmentMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 48 structSourceUnit "StructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "replaceY")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 9)
  | _ => some false

def structAbiEchoMatches : Option Bool := do
  let contract ← SourceUnit.toCoreContract? structSourceUnit "StructDemo"
  let selector :=
    SolidCore.Solidity.Source.ABI.selectorFromSignature
      "echo((uint256,uint256))"
  let tupleTy :=
    SolidCore.Solidity.Source.Ty.tuple
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.uint256 ]
  let tupleValue :=
    SolidCore.Solidity.Source.Value.tuple
      [ SolidCore.Solidity.Source.Value.word 3
      , SolidCore.Solidity.Source.Value.word 4 ]
  let calldata ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [tupleTy] [tupleValue]
  let result ←
    SolidCore.Solidity.Source.ABI.Contract.callCalldata?
      48 contract SolidCore.Solidity.Source.State.empty
      (SolidCore.Solidity.Source.wordToBytesBE
        SolidCore.Solidity.Source.selectorBytes selector ++ calldata)
  let expected ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [tupleTy] [tupleValue]
  some (result.success && result.output == expected)

def structEventTopicMatches : Option Bool := do
  let contract ← SourceUnit.toCoreContract? structSourceUnit "StructDemo"
  let event ←
    contract.eventDecls.find? (fun event => event.name == "Seen")
  let field ← event.fields.head?
  let fieldIsTuple :=
    match field.ty with
    | SolidCore.Solidity.Source.Ty.tuple
        [ SolidCore.Solidity.Source.Ty.uint256
        , SolidCore.Solidity.Source.Ty.uint256 ] => true
    | _ => false
  some
    (event.topic? ==
      some
        (SolidCore.Solidity.Source.Keccak.digestWord
          "Seen((uint256,uint256))") &&
      fieldIsTuple && !field.indexed)

def structErrorSelectorMatches : Option Bool := do
  let contract ← SourceUnit.toCoreContract? structSourceUnit "StructDemo"
  let err ←
    contract.errorDecls.find? (fun err => err.name == "Bad")
  let field ← err.fields.head?
  let fieldIsTuple :=
    match field with
    | SolidCore.Solidity.Source.Ty.tuple
        [ SolidCore.Solidity.Source.Ty.uint256
        , SolidCore.Solidity.Source.Ty.uint256 ] => true
    | _ => false
  some
    (err.selector ==
      SolidCore.Solidity.Source.ABI.selectorFromSignature
        "Bad((uint256,uint256))" &&
      fieldIsTuple)

def storageStructContract : ContractDecl :=
  { name := "StorageStructDemo"
    items :=
      [ ContractItem.stateVar
          { name := "origin"
            ty := pointTy
            visibility := some Visibility.public_ }
      , ContractItem.function
          { name := some "set"
            params :=
              [ { name := some "x", ty := Ty.uint 256 }
              , { name := some "y", ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "origin") AssignOp.assign
                    (pointConstructorNamed
                      (Expr.ident "x") (Expr.ident "y")))) }
      , ContractItem.function
          { name := some "setY"
            params := [{ name := some "y", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign
                    (Expr.member (Expr.ident "origin") "y")
                    AssignOp.assign
                    (Expr.ident "y"))) }
      , ContractItem.function
          { name := some "aliasSetY"
            params := [{ name := some "y", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "ref"
                          ty := some pointTy
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "origin"))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.member (Expr.ident "ref") "y")
                        AssignOp.assign
                        (Expr.ident "y")) ]) }
      , ContractItem.function
          { name := some "aliasSum"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "ref"
                          ty := some pointTy
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "origin"))
                  , Stmt.returnValues
                      (some
                          (Expr.binary BinaryOp.add
                            (Expr.member (Expr.ident "ref") "x")
                            (Expr.member (Expr.ident "ref") "y"))) ]) }
      , ContractItem.function
          { name := some "setPointY"
            visibility := some Visibility.internal_
            params :=
              [ { name := some "point"
                  ty := pointTy
                  location := some DataLocation.storage }
              , { name := some "y"
                  ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign
                        (Expr.member (Expr.ident "point") "y")
                        AssignOp.assign
                        (Expr.ident "y")) ]) }
      , ContractItem.function
          { name := some "sumPoint"
            visibility := some Visibility.internal_
            params :=
              [ { name := some "point"
                  ty := pointTy
                  location := some DataLocation.storage } ]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.binary BinaryOp.add
                      (Expr.member (Expr.ident "point") "x")
                      (Expr.member (Expr.ident "point") "y")))) }
      , ContractItem.function
          { name := some "internalSetY"
            params := [{ name := some "y", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.expr
                  (Expr.call
                    (Expr.ident "setPointY")
                    [ Arg.positional (Expr.ident "origin")
                    , Arg.positional (Expr.ident "y") ])) }
      , ContractItem.function
          { name := some "internalAliasSetY"
            params := [{ name := some "y", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "ref"
                          ty := some pointTy
                          location := some DataLocation.storage } ]
                      (some (Expr.ident "origin"))
                  , Stmt.expr
                      (Expr.call
                        (Expr.ident "setPointY")
                        [ Arg.positional (Expr.ident "ref")
                        , Arg.positional (Expr.ident "y") ]) ]) }
      , ContractItem.function
          { name := some "internalSum"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call
                      (Expr.ident "sumPoint")
                      [Arg.positional (Expr.ident "origin")]))) }
      , ContractItem.function
          { name := some "sum"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.binary BinaryOp.add
                      (Expr.member (Expr.ident "origin") "x")
                      (Expr.member (Expr.ident "origin") "y")))) }
      , ContractItem.function
          { name := some "clear"
            body :=
              some
                (Stmt.expr
                  (Expr.unary UnaryOp.delete (Expr.ident "origin"))) } ] }

def storageStructSourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.freeStruct pointStructDecl
      , SourceItem.contract storageStructContract ] }

def storageStructSetState : Option CoreState := do
  let result ←
    SourceUnit.callContract? 48 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "set")
      SolidCore.Solidity.Source.State.empty
      [ SolidCore.Solidity.Source.Value.word 11
      , SolidCore.Solidity.Source.Value.word 12 ]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageStructSumMatches : Option Bool := do
  let state ← storageStructSetState
  let result ←
    SourceUnit.callContract? 48 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "sum")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 23)
  | _ => some false

def storageStructFieldWriteState : Option CoreState := do
  let state ← storageStructSetState
  let result ←
    SourceUnit.callContract? 48 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "setY")
      state [SolidCore.Solidity.Source.Value.word 40]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageStructFieldWriteMatches : Option Bool := do
  let state ← storageStructFieldWriteState
  let result ←
    SourceUnit.callContract? 48 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "sum")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 51)
  | _ => some false

def storageStructAliasFieldWriteState : Option CoreState := do
  let state ← storageStructSetState
  let result ←
    SourceUnit.callContract? 48 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "aliasSetY")
      state [SolidCore.Solidity.Source.Value.word 70]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageStructAliasFieldWriteMatches : Option Bool := do
  let state ← storageStructAliasFieldWriteState
  let result ←
    SourceUnit.callContract? 48 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "sum")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 81)
  | _ => some false

def storageStructAliasReadMatches : Option Bool := do
  let state ← storageStructAliasFieldWriteState
  let result ←
    SourceUnit.callContract? 48 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "aliasSum")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 81)
  | _ => some false

def storageStructInternalParamSetState : Option CoreState := do
  let state ← storageStructSetState
  let result ←
    SourceUnit.callContract? 64 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "internalSetY")
      state [SolidCore.Solidity.Source.Value.word 50]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageStructInternalParamFieldWriteMatches : Option Bool := do
  let state ← storageStructInternalParamSetState
  let result ←
    SourceUnit.callContract? 48 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "sum")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 61)
  | _ => some false

def storageStructInternalParamAliasSetState : Option CoreState := do
  let state ← storageStructSetState
  let result ←
    SourceUnit.callContract? 64 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "internalAliasSetY")
      state [SolidCore.Solidity.Source.Value.word 60]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageStructInternalParamAliasFieldWriteMatches : Option Bool := do
  let state ← storageStructInternalParamAliasSetState
  let result ←
    SourceUnit.callContract? 48 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "sum")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 71)
  | _ => some false

def storageStructInternalParamReadMatches : Option Bool := do
  let state ← storageStructInternalParamAliasSetState
  let result ←
    SourceUnit.callContract? 64 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "internalSum")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (value == 71)
  | _ => some false

def storageStructPublicGetterMatches : Option Bool := do
  let state ← storageStructFieldWriteState
  let result ←
    SourceUnit.callContract? 48 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "origin")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] => do
      let (x, y) ← CoreValue.asWordPair? value
      some (x == 11 && y == 40)
  | _ => some false

def storageStructDeleteState : Option CoreState := do
  let state ← storageStructFieldWriteState
  let result ←
    SourceUnit.callContract? 48 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "clear")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => some state
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => none

def storageStructDeleteClears : Option Bool := do
  let state ← storageStructDeleteState
  let result ←
    SourceUnit.callContract? 48 storageStructSourceUnit "StorageStructDemo"
      (SolidCore.Solidity.Source.CallTarget.name "origin")
      state []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [value] => do
      let (x, y) ← CoreValue.asWordPair? value
      some (x == 0 && y == 0)
  | _ => some false

def storageStructAbiGetterMatches : Option Bool := do
  let contract ← SourceUnit.toCoreContract? storageStructSourceUnit
    "StorageStructDemo"
  let state ← storageStructFieldWriteState
  let selector :=
    SolidCore.Solidity.Source.ABI.selectorFromSignature "origin()"
  let result ←
    SolidCore.Solidity.Source.ABI.Contract.callCalldata?
      48 contract state
      (SolidCore.Solidity.Source.wordToBytesBE
        SolidCore.Solidity.Source.selectorBytes selector)
  let tupleTy :=
    SolidCore.Solidity.Source.Ty.tuple
      [ SolidCore.Solidity.Source.Ty.uint256
      , SolidCore.Solidity.Source.Ty.uint256 ]
  let expected ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [tupleTy]
      [SolidCore.Solidity.Source.Value.tuple
        [ SolidCore.Solidity.Source.Value.word 11
        , SolidCore.Solidity.Source.Value.word 40 ]]
  some (result.success && result.output == expected)

def internalCallContract : ContractDecl :=
  { name := "InternalCalls"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { name := some "addOne"
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.addAssign
                    (Expr.literal (Literal.number "1")))) }
      , ContractItem.function
          { name := some "run"
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.call (Expr.ident "addOne") [])
                  , Stmt.expr
                      (Expr.call (Expr.ident "addOne") []) ]) } ] }

def internalCallResult : Option CoreCallResult :=
  ContractDecl.call? 32 internalCallContract
    (SolidCore.Solidity.Source.CallTarget.name "run")
    SolidCore.Solidity.Source.State.empty []

def internalReturnCallContract : ContractDecl :=
  { name := "InternalReturn"
    items :=
      [ ContractItem.function
          { name := some "double"
            params := [{ name := some "value", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.binary BinaryOp.mul
                      (Expr.ident "value")
                      (Expr.literal (Literal.number "2"))))) }
      , ContractItem.function
          { name := some "run"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call (Expr.ident "double")
                      [Arg.positional
                        (Expr.literal (Literal.number "21"))]))) } ] }

def internalReturnCallResult : Option CoreCallResult :=
  ContractDecl.call? 32 internalReturnCallContract
    (SolidCore.Solidity.Source.CallTarget.name "run")
    SolidCore.Solidity.Source.State.empty []

def internalNamedArgsContract : ContractDecl :=
  { name := "InternalNamedArgs"
    items :=
      [ ContractItem.function
          { name := some "combine"
            params :=
              [ { name := some "left", ty := Ty.uint 256 }
              , { name := some "right", ty := Ty.uint 256 } ]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.binary BinaryOp.add
                      (Expr.binary BinaryOp.mul
                        (Expr.ident "left")
                        (Expr.literal (Literal.number "10")))
                      (Expr.ident "right")))) }
      , ContractItem.function
          { name := some "run"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call (Expr.ident "combine")
                      [ Arg.named "right"
                          (Expr.literal (Literal.number "2"))
                      , Arg.named "left"
                          (Expr.literal (Literal.number "4")) ]))) } ] }

def internalNamedArgsMatches : Option Bool := do
  let result ←
    ContractDecl.call? 32 internalNamedArgsContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 42)
  | _ => some false

def tupleVarDeclContract : ContractDecl :=
  { name := "TupleVarDecl"
    items :=
      [ ContractItem.function
          { name := some "run"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "left", ty := some (Ty.uint 256) }
                      , { name := some "right", ty := some (Ty.uint 256) } ]
                      (some
                        (Expr.tuple
                          [ TupleItem.value
                              (Expr.literal (Literal.number "4"))
                          , TupleItem.value
                              (Expr.literal (Literal.number "2")) ]))
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.ident "left")
                            (Expr.literal (Literal.number "10")))
                          (Expr.ident "right"))) ]) } ] }

def tupleVarDeclMatches : Option Bool := do
  let result ←
    ContractDecl.call? 32 tupleVarDeclContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 42)
  | _ => some false

def tupleVarDeclHoleContract : ContractDecl :=
  { name := "TupleVarDeclHole"
    items :=
      [ ContractItem.function
          { name := some "run"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "left", ty := some (Ty.uint 256) }
                      , { name := none, ty := none }
                      , { name := some "right", ty := some (Ty.uint 256) } ]
                      (some
                        (Expr.tuple
                          [ TupleItem.value
                              (Expr.literal (Literal.number "4"))
                          , TupleItem.value
                              (Expr.literal (Literal.number "99"))
                          , TupleItem.value
                              (Expr.literal (Literal.number "2")) ]))
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.ident "left")
                            (Expr.literal (Literal.number "10")))
                          (Expr.ident "right"))) ]) } ] }

def tupleVarDeclHoleMatches : Option Bool := do
  let result ←
    ContractDecl.call? 32 tupleVarDeclHoleContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 42)
  | _ => some false

def tupleAssignmentSwapContract : ContractDecl :=
  { name := "TupleAssignmentSwap"
    items :=
      [ ContractItem.function
          { name := some "run"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [{ name := some "left", ty := some (Ty.uint 256) }]
                      (some (Expr.literal (Literal.number "4")))
                  , Stmt.varDecl
                      [{ name := some "right", ty := some (Ty.uint 256) }]
                      (some (Expr.literal (Literal.number "2")))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.tuple
                          [ TupleItem.value (Expr.ident "left")
                          , TupleItem.value (Expr.ident "right") ])
                        AssignOp.assign
                        (Expr.tuple
                          [ TupleItem.value (Expr.ident "right")
                          , TupleItem.value (Expr.ident "left") ]))
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.ident "left")
                            (Expr.literal (Literal.number "10")))
                          (Expr.ident "right"))) ]) } ] }

def tupleAssignmentSwapMatches : Option Bool := do
  let result ←
    ContractDecl.call? 32 tupleAssignmentSwapContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 24)
  | _ => some false

def tupleAssignmentHoleContract : ContractDecl :=
  { name := "TupleAssignmentHole"
    items :=
      [ ContractItem.function
          { name := some "run"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [{ name := some "left", ty := some (Ty.uint 256) }]
                      (some (Expr.literal (Literal.number "0")))
                  , Stmt.varDecl
                      [{ name := some "right", ty := some (Ty.uint 256) }]
                      (some (Expr.literal (Literal.number "0")))
                  , Stmt.expr
                      (Expr.assign
                        (Expr.tuple
                          [ TupleItem.value (Expr.ident "left")
                          , TupleItem.hole
                          , TupleItem.value (Expr.ident "right") ])
                        AssignOp.assign
                        (Expr.tuple
                          [ TupleItem.value
                              (Expr.literal (Literal.number "4"))
                          , TupleItem.value
                              (Expr.literal (Literal.number "99"))
                          , TupleItem.value
                              (Expr.literal (Literal.number "2")) ]))
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.binary BinaryOp.mul
                            (Expr.ident "left")
                            (Expr.literal (Literal.number "10")))
                          (Expr.ident "right"))) ]) } ] }

def tupleAssignmentHoleMatches : Option Bool := do
  let result ←
    ContractDecl.call? 32 tupleAssignmentHoleContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 42)
  | _ => some false

def internalVarDeclCallContract : ContractDecl :=
  { name := "InternalVarDecl"
    items :=
      [ ContractItem.function
          { name := some "double"
            params := [{ name := some "value", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.binary BinaryOp.mul
                      (Expr.ident "value")
                      (Expr.literal (Literal.number "2"))))) }
      , ContractItem.function
          { name := some "run"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [{ name := some "y", ty := some (Ty.uint 256) }]
                      (some
                        (Expr.call (Expr.ident "double")
                          [Arg.positional
                            (Expr.literal (Literal.number "5"))]))
                  , Stmt.returnValues (some (Expr.ident "y")) ]) } ] }

def internalVarDeclCallResult : Option CoreCallResult :=
  ContractDecl.call? 32 internalVarDeclCallContract
    (SolidCore.Solidity.Source.CallTarget.name "run")
    SolidCore.Solidity.Source.State.empty []

def internalMultiVarDeclCallContract : ContractDecl :=
  { name := "InternalMultiVarDecl"
    items :=
      [ ContractItem.function
          { name := some "pair"
            params := [{ name := some "value", ty := Ty.uint 256 }]
            returns :=
              [ { name := some "left", ty := Ty.uint 256 }
              , { name := some "right", ty := Ty.uint 256 } ]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.tuple
                      [ TupleItem.value (Expr.ident "value")
                      , TupleItem.value
                          (Expr.binary BinaryOp.add
                            (Expr.ident "value")
                            (Expr.literal (Literal.number "1"))) ]))) }
      , ContractItem.function
          { name := some "run"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "a", ty := some (Ty.uint 256) }
                      , { name := some "b", ty := some (Ty.uint 256) } ]
                      (some
                        (Expr.call (Expr.ident "pair")
                          [Arg.positional
                            (Expr.literal (Literal.number "20"))]))
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.ident "a")
                          (Expr.ident "b"))) ]) } ] }

def internalMultiVarDeclCallMatches : Option Bool := do
  let result ←
    ContractDecl.call? 32 internalMultiVarDeclCallContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 41)
  | _ => some false

def freeDoubleFunction : FunctionDecl :=
  { name := some "double"
    params := [{ name := some "value", ty := Ty.uint 256 }]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    mutability := StateMutability.pure
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.binary BinaryOp.mul
              (Expr.ident "value")
              (Expr.literal (Literal.number "2"))))) }

def freeFunctionCallerContract : ContractDecl :=
  { name := "FreeFunctionCaller"
    items :=
      [ ContractItem.function
          { name := some "run"
            params := [{ name := some "value", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call (Expr.ident "double")
                      [Arg.positional (Expr.ident "value")]))) } ] }

def freeFunctionUnit : SourceUnit :=
  { items :=
      [ SourceItem.freeFunction freeDoubleFunction
      , SourceItem.contract freeFunctionCallerContract ] }

def freeFunctionCallMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 freeFunctionUnit "FreeFunctionCaller"
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 21]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 42)
  | _ => some false

def freeNamedCombineFunction : FunctionDecl :=
  { name := some "combine"
    params :=
      [ { name := some "left", ty := Ty.uint 256 }
      , { name := some "right", ty := Ty.uint 256 } ]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    mutability := StateMutability.pure
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.binary BinaryOp.add
              (Expr.binary BinaryOp.mul
                (Expr.ident "left")
                (Expr.literal (Literal.number "10")))
              (Expr.ident "right")))) }

def freeNamedArgsUnit : SourceUnit :=
  { items :=
      [ SourceItem.freeFunction freeNamedCombineFunction
      , SourceItem.contract
          { name := "FreeNamedArgs"
            items :=
              [ ContractItem.function
                  { name := some "run"
                    returns := [{ name := some "out", ty := Ty.uint 256 }]
                    body :=
                      some
                        (Stmt.returnValues
                          (some
                            (Expr.call (Expr.ident "combine")
                              [ Arg.named "right"
                                  (Expr.literal (Literal.number "2"))
                              , Arg.named "left"
                                  (Expr.literal (Literal.number "4")) ]))) } ] } ] }

def freeNamedArgsMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 freeNamedArgsUnit "FreeNamedArgs"
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 42)
  | _ => some false

def freeFunctionStorageIsolationFunction : FunctionDecl :=
  { name := some "readX"
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    mutability := StateMutability.view
    body := some (Stmt.returnValues (some (Expr.ident "x"))) }

def freeFunctionStorageIsolationContract : ContractDecl :=
  { name := "FreeStorageIsolation"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { name := some "run"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.call (Expr.ident "readX") []))) } ] }

def freeFunctionStorageIsolationUnit : SourceUnit :=
  { items :=
      [ SourceItem.freeFunction freeFunctionStorageIsolationFunction
      , SourceItem.contract freeFunctionStorageIsolationContract ] }

def freeFunctionDoesNotCaptureStorageMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 freeFunctionStorageIsolationUnit
      "FreeStorageIsolation"
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _ _ => some true
  | _ => some false

def freeErrorUnit : SourceUnit :=
  { items :=
      [ SourceItem.freeError
          { name := "TooSmall"
            params := [{ name := some "actual", ty := Ty.uint 256 }] }
      , SourceItem.contract
          { name := "UsesFreeError"
            items :=
              [ ContractItem.function
                  { name := some "check"
                    params := [{ name := some "value", ty := Ty.uint 256 }]
                    body :=
                      some
                        (Stmt.expr
                          (Expr.call (Expr.ident "require")
                            [ Arg.positional
                                (Expr.binary BinaryOp.gt
                                  (Expr.ident "value")
                                  (Expr.literal (Literal.number "10")))
                            , Arg.positional
                                (Expr.call (Expr.ident "TooSmall")
                                  [Arg.positional (Expr.ident "value")]) ])) } ] } ] }

def freeErrorAbiMatches : Option Bool := do
  let contract ← SourceUnit.toCoreContract? freeErrorUnit "UsesFreeError"
  let function ← contract.findFunctionByName? "check"
  let calldata ←
    SolidCore.Solidity.Source.ABI.calldataFor? function
      [SolidCore.Solidity.Source.Value.word 4]
  let result ←
    SolidCore.Solidity.Source.ABI.Contract.callCalldata?
      16 contract SolidCore.Solidity.Source.State.empty calldata
  let payload ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 4]
  let selector :=
    SolidCore.Solidity.Source.ABI.encodeSelector
      (SolidCore.Solidity.Source.ABI.selectorFromSignature
        "TooSmall(uint256)")
  some (!result.success && result.output == selector ++ payload)

def fileConstantContractUnit : SourceUnit :=
  { items :=
      [ SourceItem.freeConstant
          { name := "FILE_TOP"
            ty := Ty.uint 256
            mutability := VarMutability.constant
            init := some (Expr.literal (Literal.number "40")) }
      , SourceItem.contract
          { name := "UsesFileConstant"
            items :=
              [ ContractItem.function
                  { name := some "run"
                    returns := [{ name := some "out", ty := Ty.uint 256 }]
                    mutability := StateMutability.pure
                    body :=
                      some
                        (Stmt.returnValues
                          (some
                            (Expr.binary BinaryOp.add
                              (Expr.ident "FILE_TOP")
                              (Expr.literal (Literal.number "2"))))) } ] } ] }

def fileConstantContractMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 fileConstantContractUnit
      "UsesFileConstant"
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 42)
  | _ => some false

def fileConstantFreeFunction : FunctionDecl :=
  { name := some "addShared"
    params := [{ name := some "value", ty := Ty.uint 256 }]
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    mutability := StateMutability.pure
    body :=
      some
        (Stmt.returnValues
          (some
            (Expr.binary BinaryOp.add
              (Expr.ident "value")
              (Expr.ident "SHARED")))) }

def fileConstantShadowingUnit : SourceUnit :=
  { items :=
      [ SourceItem.freeConstant
          { name := "SHARED"
            ty := Ty.uint 256
            mutability := VarMutability.constant
            init := some (Expr.literal (Literal.number "40")) }
      , SourceItem.freeFunction fileConstantFreeFunction
      , SourceItem.contract
          { name := "FileConstantShadowing"
            items :=
              [ ContractItem.stateVar
                  { name := "SHARED"
                    ty := Ty.uint 256
                    mutability := VarMutability.constant
                    init := some (Expr.literal (Literal.number "100")) }
              , ContractItem.function
                  { name := some "fromFree"
                    returns := [{ name := some "out", ty := Ty.uint 256 }]
                    mutability := StateMutability.pure
                    body :=
                      some
                        (Stmt.returnValues
                          (some
                            (Expr.call (Expr.ident "addShared")
                              [Arg.positional
                                (Expr.literal (Literal.number "2"))]))) }
              , ContractItem.function
                  { name := some "fromContract"
                    returns := [{ name := some "out", ty := Ty.uint 256 }]
                    mutability := StateMutability.pure
                    body :=
                      some
                        (Stmt.returnValues
                          (some (Expr.ident "SHARED"))) } ] } ] }

def fileConstantFreeFunctionMatches : Option Bool := do
  let freeResult ←
    SourceUnit.callContract? 32 fileConstantShadowingUnit
      "FileConstantShadowing"
      (SolidCore.Solidity.Source.CallTarget.name "fromFree")
      SolidCore.Solidity.Source.State.empty []
  let contractResult ←
    SourceUnit.callContract? 32 fileConstantShadowingUnit
      "FileConstantShadowing"
      (SolidCore.Solidity.Source.CallTarget.name "fromContract")
      SolidCore.Solidity.Source.State.empty []
  match freeResult, contractResult with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word freeValue],
    SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word contractValue] =>
      some
        (SolidCore.Solidity.Source.wordEq freeValue 42 &&
          SolidCore.Solidity.Source.wordEq contractValue 100)
  | _, _ => some false

def fileConstantConstructorUnit : SourceUnit :=
  { items :=
      [ SourceItem.freeConstant
          { name := "FILE_TOP"
            ty := Ty.uint 256
            mutability := VarMutability.constant
            init := some (Expr.literal (Literal.number "40")) }
      , SourceItem.contract
          { name := "FileConstantConstructor"
            items :=
              [ ContractItem.stateVar
                  { name := "x"
                    ty := Ty.uint 256
                    init :=
                      some
                        (Expr.binary BinaryOp.add
                          (Expr.ident "FILE_TOP")
                          (Expr.literal (Literal.number "1"))) } ] } ] }

def fileConstantConstructorMatches : Option Bool := do
  let result ←
    SourceUnit.constructContract? 32 fileConstantConstructorUnit
      "FileConstantConstructor"
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 41)
  | _ => some false

def constantReadContract : ContractDecl :=
  { name := "ConstantRead"
    items :=
      [ ContractItem.stateVar
          { name := "LIMIT"
            ty := Ty.uint 256
            visibility := some Visibility.public_
            mutability := VarMutability.constant
            init := some (Expr.literal (Literal.number "41")) }
      , ContractItem.function
          { name := some "run"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            mutability := StateMutability.pure
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.binary BinaryOp.add
                      (Expr.ident "LIMIT")
                      (Expr.literal (Literal.number "1"))))) } ] }

def constantReadMatches : Option Bool := do
  let result ←
    ContractDecl.call? 32 constantReadContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 42)
  | _ => some false

def constantPublicGetterMatches : Option Bool := do
  let result ←
    ContractDecl.call? 32 constantReadContract
      (SolidCore.Solidity.Source.CallTarget.name "LIMIT")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 41)
  | _ => some false

def constantLayoutContract : ContractDecl :=
  { name := "ConstantLayout"
    items :=
      [ ContractItem.stateVar
          { name := "C"
            ty := Ty.uint 256
            mutability := VarMutability.constant
            init := some (Expr.literal (Literal.number "1")) }
      , ContractItem.stateVar { name := "a", ty := Ty.uint 256 }
      , ContractItem.stateVar
          { name := "I"
            ty := Ty.uint 256
            mutability := VarMutability.immutable
            init := some (Expr.literal (Literal.number "2")) }
      , ContractItem.stateVar { name := "b", ty := Ty.uint 256 } ] }

def constantStorageLayoutMatches : Option Bool := do
  let contract ← ContractDecl.toCore? constantLayoutContract
  match contract.storageFields with
  | [a, b] =>
      some
        (a.name == "a" &&
          SolidCore.Solidity.Source.wordEq a.slot 0 &&
          b.name == "b" &&
          SolidCore.Solidity.Source.wordEq b.slot 1)
  | _ => some false

def constantInitializerContract : ContractDecl :=
  { name := "ConstantInitializer"
    items :=
      [ ContractItem.stateVar
          { name := "BASE"
            ty := Ty.uint 256
            mutability := VarMutability.constant
            init := some (Expr.literal (Literal.number "5")) }
      , ContractItem.stateVar
          { name := "x"
            ty := Ty.uint 256
            init :=
              some
                (Expr.binary BinaryOp.add
                  (Expr.ident "BASE")
                  (Expr.literal (Literal.number "1"))) } ] }

def constantInitializerMatches : Option Bool := do
  let result ←
    ContractDecl.construct? 32 constantInitializerContract
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 6)
  | _ => some false

def immutableConstructorContract : ContractDecl :=
  { name := "ImmutableConstructor"
    items :=
      [ ContractItem.stateVar
          { name := "SEED"
            ty := Ty.uint 256
            visibility := some Visibility.public_
            mutability := VarMutability.immutable
            init := some (Expr.literal (Literal.number "3")) }
      , ContractItem.stateVar
          { name := "x"
            ty := Ty.uint 256
            visibility := some Visibility.public_
            mutability := VarMutability.immutable }
      , ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "value", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.binary BinaryOp.add
                      (Expr.ident "value")
                      (Expr.ident "SEED")))) }
      , ContractItem.function
          { name := some "sum"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            mutability := StateMutability.view
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.binary BinaryOp.add
                      (Expr.ident "x")
                      (Expr.ident "SEED")))) }
      , ContractItem.function
          { name := some "mutate"
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.literal (Literal.number "1")))) } ] }

def immutableConstructorMatches : Option Bool := do
  let deployed ←
    ContractDecl.construct? 32 immutableConstructorContract
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 9]
  match deployed with
  | SolidCore.Solidity.Source.CallResult.returned state _ => do
      let result ←
        ContractDecl.call? 32 immutableConstructorContract
          (SolidCore.Solidity.Source.CallTarget.name "sum") state []
      match result with
      | SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word value] =>
          some (SolidCore.Solidity.Source.wordEq value 15)
      | _ => some false
  | _ => some false

def immutablePublicGetterMatches : Option Bool := do
  let deployed ←
    ContractDecl.construct? 32 immutableConstructorContract
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 9]
  match deployed with
  | SolidCore.Solidity.Source.CallResult.returned state _ => do
      let result ←
        ContractDecl.call? 32 immutableConstructorContract
          (SolidCore.Solidity.Source.CallTarget.name "x") state []
      match result with
      | SolidCore.Solidity.Source.CallResult.returned _
          [SolidCore.Solidity.Source.Value.word value] =>
          some (SolidCore.Solidity.Source.wordEq value 12)
      | _ => some false
  | _ => some false

def immutableRuntimeWriteRejectsMatches : Option Bool := do
  let deployed ←
    ContractDecl.construct? 32 immutableConstructorContract
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 9]
  match deployed with
  | SolidCore.Solidity.Source.CallResult.returned state _ => do
      let result ←
        ContractDecl.call? 32 immutableConstructorContract
          (SolidCore.Solidity.Source.CallTarget.name "mutate") state []
      match result with
      | SolidCore.Solidity.Source.CallResult.reverted revertedState _ =>
          match revertedState.immutable? "x", state.immutable? "x" with
          | some (SolidCore.Solidity.Source.Value.word revertedValue),
              some (SolidCore.Solidity.Source.Value.word originalValue) =>
              some (SolidCore.Solidity.Source.wordEq
                revertedValue originalValue)
          | _, _ => some false
      | _ => some false
  | _ => some false

def constructorContract : ContractDecl :=
  { name := "Constructed"
    items :=
      [ ContractItem.stateVar
          { name := "x"
            ty := Ty.uint 256
            init := some (Expr.literal (Literal.number "1")) }
      , ContractItem.stateVar { name := "y", ty := Ty.uint 256 }
      , ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "value", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "y") AssignOp.assign
                    (Expr.ident "value"))) } ] }

def constructorDeployResult : Option CoreCallResult :=
  ContractDecl.construct? 16 constructorContract
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 42]

def revertingConstructorContract : ContractDecl :=
  { name := "Bad"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { kind := FunctionKind.constructor
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign (Expr.ident "x") AssignOp.assign
                        (Expr.literal (Literal.number "7")))
                  , Stmt.expr
                      (Expr.call (Expr.ident "require")
                        [Arg.positional (Expr.literal (Literal.bool false))]) ]) } ] }

def revertingConstructorDeployResult : Option CoreCallResult :=
  ContractDecl.construct? 16 revertingConstructorContract
    SolidCore.Solidity.Source.State.empty []

def constructorInternalCallContract : ContractDecl :=
  { name := "CtorInternalCall"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { name := some "double"
            params := [{ name := some "value", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.binary BinaryOp.mul
                      (Expr.ident "value")
                      (Expr.literal (Literal.number "2"))))) }
      , ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "seed", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.call (Expr.ident "double")
                      [Arg.positional (Expr.ident "seed")]))) } ] }

def constructorInternalCallMatches : Option Bool := do
  let result ←
    ContractDecl.construct? 32 constructorInternalCallContract
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 21]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 42)
  | _ => some false

def constructorFreeFunctionContract : ContractDecl :=
  { name := "CtorFreeFunction"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "seed", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.call (Expr.ident "double")
                      [Arg.positional (Expr.ident "seed")]))) } ] }

def constructorFreeFunctionUnit : SourceUnit :=
  { items :=
      [ SourceItem.freeFunction freeDoubleFunction
      , SourceItem.contract constructorFreeFunctionContract ] }

def constructorFreeFunctionMatches : Option Bool := do
  let result ←
    SourceUnit.constructContract? 32 constructorFreeFunctionUnit
      "CtorFreeFunction"
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 21]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 42)
  | _ => some false

def inheritedBaseContract : ContractDecl :=
  { name := "Base"
    items :=
      [ ContractItem.stateVar
          { name := "x"
            ty := Ty.uint 256
            init := some (Expr.literal (Literal.number "5")) }
      , ContractItem.function
          { name := some "setX"
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.literal (Literal.number "5")))) }
      , ContractItem.function
          { name := some "value"
            returns := [{ ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.literal (Literal.number "1")))) } ] }

def inheritedDerivedContract : ContractDecl :=
  { name := "Derived"
    bases := [{ base := { segments := ["Base"] } }]
    items :=
      [ ContractItem.stateVar
          { name := "y"
            ty := Ty.uint 256
            init := some (Expr.literal (Literal.number "9")) }
      , ContractItem.function
          { name := some "setY"
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "y") AssignOp.assign
                    (Expr.literal (Literal.number "9")))) }
      , ContractItem.function
          { name := some "value"
            returns := [{ ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.literal (Literal.number "2")))) } ] }

def inheritanceUnit : SourceUnit :=
  { items :=
      [ SourceItem.contract inheritedBaseContract
      , SourceItem.contract inheritedDerivedContract ] }

def inheritedStorageFields : Option (List CoreStorageField) := do
  let contract ← SourceUnit.toCoreContract? inheritanceUnit "Derived"
  some contract.storageFields

def inheritedConstructorDeployResult : Option CoreCallResult :=
  SourceUnit.constructContract? 16 inheritanceUnit "Derived"
    SolidCore.Solidity.Source.State.empty []

def baseConstructorArgBase : ContractDecl :=
  { name := "BaseArg"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "value", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.ident "value"))) } ] }

def baseConstructorArgDerived : ContractDecl :=
  { name := "DerivedArg"
    bases :=
      [ { base := { segments := ["BaseArg"] }
          args := [Expr.literal (Literal.number "12")] } ]
    items :=
      [ ContractItem.stateVar { name := "y", ty := Ty.uint 256 }
      , ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "value", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "y") AssignOp.assign
                    (Expr.ident "value"))) } ] }

def baseConstructorArgUnit : SourceUnit :=
  { items :=
      [ SourceItem.contract baseConstructorArgBase
      , SourceItem.contract baseConstructorArgDerived ] }

def inheritedBaseConstructorArgDeployResult : Option CoreCallResult :=
  SourceUnit.constructContract? 16 baseConstructorArgUnit "DerivedArg"
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word 34]

def baseConstructorModifierArgDerived : ContractDecl :=
  { name := "DerivedModifierArg"
    bases := [{ base := { segments := ["BaseArg"] } }]
    items :=
      [ ContractItem.stateVar { name := "y", ty := Ty.uint 256 }
      , ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "seed", ty := Ty.uint 256 }]
            modifiers :=
              [ { target := { segments := ["BaseArg"] }
                  args :=
                    [ Arg.positional
                        (Expr.binary BinaryOp.mul
                          (Expr.ident "seed")
                          (Expr.ident "seed")) ] } ]
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "y") AssignOp.assign
                    (Expr.binary BinaryOp.add
                      (Expr.ident "seed")
                      (Expr.literal (Literal.number "1"))))) } ] }

def baseConstructorModifierArgUnit : SourceUnit :=
  { items :=
      [ SourceItem.contract baseConstructorArgBase
      , SourceItem.contract baseConstructorModifierArgDerived ] }

def inheritedBaseConstructorModifierArgMatches : Option Bool := do
  let result ←
    SourceUnit.constructContract? 32 baseConstructorModifierArgUnit
      "DerivedModifierArg"
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 6]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      some
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 36 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 7)
  | _ => some false

def baseConstructorDeferredArgMiddle : ContractDecl :=
  { name := "DeferredArgMiddle"
    bases := [{ base := { segments := ["BaseArg"] } }]
    items := [] }

def baseConstructorDeferredArgDerived : ContractDecl :=
  { name := "DeferredArgDerived"
    bases := [{ base := { segments := ["DeferredArgMiddle"] } }]
    items :=
      [ ContractItem.stateVar { name := "y", ty := Ty.uint 256 }
      , ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "seed", ty := Ty.uint 256 }]
            modifiers :=
              [ { target := { segments := ["BaseArg"] }
                  args :=
                    [ Arg.positional
                        (Expr.binary BinaryOp.add
                          (Expr.ident "seed")
                          (Expr.literal (Literal.number "10"))) ] } ]
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "y") AssignOp.assign
                    (Expr.ident "seed"))) } ] }

def baseConstructorDeferredArgUnit : SourceUnit :=
  { items :=
      [ SourceItem.contract baseConstructorArgBase
      , SourceItem.contract baseConstructorDeferredArgMiddle
      , SourceItem.contract baseConstructorDeferredArgDerived ] }

def inheritedBaseConstructorDeferredArgMatches : Option Bool := do
  let result ←
    SourceUnit.constructContract? 32 baseConstructorDeferredArgUnit
      "DeferredArgDerived"
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 6]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      some
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 16 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 6)
  | _ => some false

def inheritedBaseFunctionCallResult : Option CoreCallResult :=
  SourceUnit.callContract? 16 inheritanceUnit "Derived"
    (SolidCore.Solidity.Source.CallTarget.name "setX")
    SolidCore.Solidity.Source.State.empty []

def derivedFunctionStorageCallResult : Option CoreCallResult :=
  SourceUnit.callContract? 16 inheritanceUnit "Derived"
    (SolidCore.Solidity.Source.CallTarget.name "setY")
    SolidCore.Solidity.Source.State.empty []

def derivedOverrideCallResult : Option CoreCallResult :=
  SourceUnit.callContract? 16 inheritanceUnit "Derived"
    (SolidCore.Solidity.Source.CallTarget.name "value")
    SolidCore.Solidity.Source.State.empty []

def superBaseContract : ContractDecl :=
  { name := "SuperBase"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.function
          { name := some "setX"
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.literal (Literal.number "5")))) }
      , ContractItem.function
          { name := some "value"
            returns := [{ ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.literal (Literal.number "1")))) } ] }

def superDerivedContract : ContractDecl :=
  { name := "SuperDerived"
    bases := [{ base := { segments := ["SuperBase"] } }]
    items :=
      [ ContractItem.function
          { name := some "setViaSuper"
            body :=
              some
                (Stmt.expr
                  (Expr.call
                    (Expr.member (Expr.ident "super") "setX") [])) }
      , ContractItem.function
          { name := some "value"
            returns := [{ ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [{ name := some "base", ty := some (Ty.uint 256) }]
                      (some
                        (Expr.call
                          (Expr.member (Expr.ident "super") "value") []))
                  , Stmt.returnValues
                      (some
                        (Expr.binary BinaryOp.add
                          (Expr.ident "base")
                          (Expr.literal (Literal.number "2")))) ]) } ] }

def superSourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.contract superBaseContract
      , SourceItem.contract superDerivedContract ] }

def superValueCallMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 superSourceUnit "SuperDerived"
      (SolidCore.Solidity.Source.CallTarget.name "value")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 3)
  | _ => some false

def superStorageCallMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 superSourceUnit "SuperDerived"
      (SolidCore.Solidity.Source.CallTarget.name "setViaSuper")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 5)
  | _ => some false

def explicitBaseLeftContract : ContractDecl :=
  { name := "ExplicitBaseLeft"
    items :=
      [ ContractItem.function
          { name := some "value"
            returns := [{ ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.literal (Literal.number "11")))) } ] }

def explicitBaseRightContract : ContractDecl :=
  { name := "ExplicitBaseRight"
    items :=
      [ ContractItem.function
          { name := some "value"
            returns := [{ ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.literal (Literal.number "22")))) } ] }

def explicitBaseFinalContract : ContractDecl :=
  { name := "ExplicitBaseFinal"
    bases :=
      [ { base := { segments := ["ExplicitBaseLeft"] } }
      , { base := { segments := ["ExplicitBaseRight"] } } ]
    items :=
      [ ContractItem.function
          { name := some "directLeft"
            returns := [{ ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call
                      (Expr.member (Expr.ident "ExplicitBaseLeft") "value")
                      []))) }
      , ContractItem.function
          { name := some "directRight"
            returns := [{ ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call
                      (Expr.member (Expr.ident "ExplicitBaseRight") "value")
                      []))) }
      , ContractItem.function
          { name := some "virtualValue"
            returns := [{ ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.call (Expr.ident "value") []))) } ] }

def explicitBaseSourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.contract explicitBaseLeftContract
      , SourceItem.contract explicitBaseRightContract
      , SourceItem.contract explicitBaseFinalContract ] }

def explicitBaseCallResult? (target : Name) : Option CoreCallResult :=
  SourceUnit.callContract? 32 explicitBaseSourceUnit "ExplicitBaseFinal"
    (SolidCore.Solidity.Source.CallTarget.name target)
    SolidCore.Solidity.Source.State.empty []

def explicitBaseReturnedWordMatches (target : Name) (expected : Word) :
    Option Bool := do
  let result ← explicitBaseCallResult? target
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value expected)
  | _ => some false

def explicitBaseDirectLeftMatches : Option Bool :=
  explicitBaseReturnedWordMatches "directLeft" 11

def explicitBaseDirectRightMatches : Option Bool :=
  explicitBaseReturnedWordMatches "directRight" 22

def explicitBaseVirtualDispatchMatches : Option Bool :=
  explicitBaseReturnedWordMatches "virtualValue" 22

def c3RootContract : ContractDecl :=
  { name := "C3Root" }

def c3LeftContract : ContractDecl :=
  { name := "C3Left"
    bases := [{ base := { segments := ["C3Root"] } }] }

def c3RightContract : ContractDecl :=
  { name := "C3Right"
    bases := [{ base := { segments := ["C3Root"] } }] }

def c3FinalContract : ContractDecl :=
  { name := "C3Final"
    bases :=
      [ { base := { segments := ["C3Left"] } }
      , { base := { segments := ["C3Right"] } } ] }

def c3Contracts : List ContractDecl :=
  [c3RootContract, c3LeftContract, c3RightContract, c3FinalContract]

def c3DispatchOrderNames : Option (List Name) := do
  let order ← ContractDecl.dispatchOrder? c3Contracts c3FinalContract
  some (order.map ContractDecl.name)

def c3DispatchOrderMatches : Option Bool := do
  let names ← c3DispatchOrderNames
  some (names == ["C3Final", "C3Right", "C3Left", "C3Root"])

def c3InconsistentXContract : ContractDecl :=
  { name := "C3InconsistentX" }

def c3InconsistentAContract : ContractDecl :=
  { name := "C3InconsistentA"
    bases := [{ base := { segments := ["C3InconsistentX"] } }] }

def c3InconsistentCContract : ContractDecl :=
  { name := "C3InconsistentC"
    bases :=
      [ { base := { segments := ["C3InconsistentA"] } }
      , { base := { segments := ["C3InconsistentX"] } } ] }

def c3InconsistentContracts : List ContractDecl :=
  [ c3InconsistentXContract
  , c3InconsistentAContract
  , c3InconsistentCContract ]

def c3InconsistentRejected : Bool :=
  match ContractDecl.dispatchOrder?
      c3InconsistentContracts c3InconsistentCContract with
  | none => true
  | some _ => false

def superChainRootContract : ContractDecl :=
  { name := "SuperChainRoot"
    items :=
      [ ContractItem.function
          { name := some "value"
            returns := [{ ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some (Expr.literal (Literal.number "77")))) } ] }

def superChainMidContract : ContractDecl :=
  { name := "SuperChainMid"
    bases := [{ base := { segments := ["SuperChainRoot"] } }]
    items :=
      [ ContractItem.function
          { name := some "value"
            returns := [{ ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call
                      (Expr.member (Expr.ident "super") "value")
                      []))) } ] }

def superChainTopContract : ContractDecl :=
  { name := "SuperChainTop"
    bases := [{ base := { segments := ["SuperChainMid"] } }]
    items :=
      [ ContractItem.function
          { name := some "value"
            returns := [{ ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call
                      (Expr.member (Expr.ident "super") "value")
                      []))) } ] }

def superChainSourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.contract superChainRootContract
      , SourceItem.contract superChainMidContract
      , SourceItem.contract superChainTopContract ] }

def superChainValueMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 64 superChainSourceUnit "SuperChainTop"
      (SolidCore.Solidity.Source.CallTarget.name "value")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 77)
  | _ => some false

def bumpModifier : ModifierDecl :=
  { name := "bump"
    body :=
      some
        (Stmt.block
          [ Stmt.expr
              (Expr.assign (Expr.ident "x") AssignOp.addAssign
                (Expr.literal (Literal.number "1")))
          , Stmt.modifierPlaceholder
          , Stmt.expr
              (Expr.assign (Expr.ident "x") AssignOp.addAssign
                (Expr.literal (Literal.number "1"))) ]) }

def runWithModifier : FunctionDecl :=
  { name := some "run"
    modifiers := [{ target := { segments := ["bump"] } }]
    body :=
      some
        (Stmt.block
          [ Stmt.expr
              (Expr.assign (Expr.ident "x") AssignOp.addAssign
                (Expr.literal (Literal.number "3"))) ]) }

def modifierContract : ContractDecl :=
  { name := "C"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.modifierDecl bumpModifier
      , ContractItem.function runWithModifier ] }

def modifierCallResult : Option CoreCallResult :=
  ContractDecl.call? 32 modifierContract
    (SolidCore.Solidity.Source.CallTarget.name "run")
    SolidCore.Solidity.Source.State.empty []

def namedArgsModifier : ModifierDecl :=
  { name := "bumpBy"
    params :=
      [ { name := some "left", ty := Ty.uint 256 }
      , { name := some "right", ty := Ty.uint 256 } ]
    body :=
      some
        (Stmt.block
          [ Stmt.expr
              (Expr.assign (Expr.ident "x") AssignOp.addAssign
                (Expr.binary BinaryOp.add
                  (Expr.binary BinaryOp.mul
                    (Expr.ident "left")
                    (Expr.literal (Literal.number "10")))
                  (Expr.ident "right")))
          , Stmt.modifierPlaceholder ]) }

def namedArgsModifierFunction : FunctionDecl :=
  { name := some "run"
    modifiers :=
      [ { target := { segments := ["bumpBy"] }
          args :=
            [ Arg.named "right" (Expr.literal (Literal.number "2"))
            , Arg.named "left" (Expr.literal (Literal.number "4")) ] } ]
    body := some Stmt.empty }

def namedArgsModifierContract : ContractDecl :=
  { name := "NamedModifierArgs"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.modifierDecl namedArgsModifier
      , ContractItem.function namedArgsModifierFunction ] }

def namedArgsModifierMatches : Option Bool := do
  let result ←
    ContractDecl.call? 32 namedArgsModifierContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 42)
  | _ => some false

def afterReturnModifier : ModifierDecl :=
  { name := "afterReturn"
    body :=
      some
        (Stmt.block
          [ Stmt.modifierPlaceholder
          , Stmt.expr
              (Expr.assign (Expr.ident "x") AssignOp.assign
                (Expr.literal (Literal.number "0"))) ]) }

def returnsThroughModifierFunction : FunctionDecl :=
  { name := some "run"
    returns := [{ name := some "out", ty := Ty.uint 256 }]
    modifiers := [{ target := { segments := ["afterReturn"] } }]
    body :=
      some
        (Stmt.block
          [ Stmt.expr
              (Expr.assign (Expr.ident "x") AssignOp.assign
                (Expr.literal (Literal.number "7")))
          , Stmt.returnValues
              (some (Expr.literal (Literal.number "11"))) ]) }

def returnsThroughModifierContract : ContractDecl :=
  { name := "ReturnThrough"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.modifierDecl afterReturnModifier
      , ContractItem.function returnsThroughModifierFunction ] }

def returnsThroughModifierCallResult : Option CoreCallResult :=
  ContractDecl.call? 32 returnsThroughModifierContract
    (SolidCore.Solidity.Source.CallTarget.name "run")
    SolidCore.Solidity.Source.State.empty []

def tryCatchAroundModifier : ModifierDecl :=
  { name := "aroundTry"
    body :=
      some
        (Stmt.tryCatchReturns
          (Expr.call (Expr.member (Expr.ident "target") "ping") [])
          [{ name := some "seen", ty := Ty.uint 256 }]
          (Stmt.block
            [ Stmt.expr
                (Expr.assign (Expr.ident "mark") AssignOp.assign
                  (Expr.ident "seen"))
            , Stmt.modifierPlaceholder ])
          [ CatchClause.clause none []
              (Stmt.block
                [ Stmt.expr
                    (Expr.assign (Expr.ident "mark") AssignOp.assign
                      (Expr.literal (Literal.number "99")))
                , Stmt.modifierPlaceholder ]) ]) }

def tryCatchAroundModifierFunction : FunctionDecl :=
  { name := some "run"
    params := [{ name := some "target", ty := Ty.address false }]
    modifiers := [{ target := { segments := ["aroundTry"] } }]
    body :=
      some
        (Stmt.expr
          (Expr.assign (Expr.ident "x") AssignOp.assign
            (Expr.literal (Literal.number "7")))) }

def tryCatchAroundModifierContract : ContractDecl :=
  { name := "TryCatchModifier"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.stateVar { name := "mark", ty := Ty.uint 256 }
      , ContractItem.modifierDecl tryCatchAroundModifier
      , ContractItem.function tryCatchAroundModifierFunction ] }

def tryCatchAroundModifierSuccessMatches : Option Bool := do
  let contract ← ContractDecl.toCore? tryCatchAroundModifierContract
  let function ← contract.findFunctionByName? "run"
  let calldata ← externalCalldata? "ping()" [] []
  let output ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 42]
  let result ←
    SolidCore.Solidity.Source.FunctionDef.call? 64
      { contract.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := calldata
              value := 0
              success := true
              output := output } ] }
      function SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      some
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 7 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 42)
  | _ => some false

def tryCatchAroundModifierCatchMatches : Option Bool := do
  let contract ← ContractDecl.toCore? tryCatchAroundModifierContract
  let function ← contract.findFunctionByName? "run"
  let calldata ← externalCalldata? "ping()" [] []
  let result ←
    SolidCore.Solidity.Source.FunctionDef.call? 64
      { contract.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := calldata
              value := 0
              success := false
              output := [0xca, 0xfe] } ] }
      function SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      some
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 7 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 99)
  | _ => some false

def directExternalCallModifier : ModifierDecl :=
  { name := "fetchBefore"
    params := [{ name := some "watched", ty := Ty.address false }]
    body :=
      some
        (Stmt.block
          [ Stmt.varDecl
              [{ name := some "seen", ty := some (Ty.uint 256) }]
              (some
                (Expr.call
                  (Expr.member (Expr.ident "watched") "get") []))
          , Stmt.expr
              (Expr.assign (Expr.ident "mark") AssignOp.assign
                (Expr.ident "seen"))
          , Stmt.modifierPlaceholder ]) }

def directExternalCallModifierFunction : FunctionDecl :=
  { name := some "run"
    params := [{ name := some "target", ty := Ty.address false }]
    modifiers :=
      [ { target := { segments := ["fetchBefore"] }
          args := [Arg.positional (Expr.ident "target")] } ]
    body :=
      some
        (Stmt.expr
          (Expr.assign (Expr.ident "x") AssignOp.assign
            (Expr.literal (Literal.number "7")))) }

def directExternalCallModifierContract : ContractDecl :=
  { name := "DirectExternalModifier"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.stateVar { name := "mark", ty := Ty.uint 256 }
      , ContractItem.modifierDecl directExternalCallModifier
      , ContractItem.function directExternalCallModifierFunction ] }

def directExternalCallModifierMatches : Option Bool := do
  let contract ← ContractDecl.toCore? directExternalCallModifierContract
  let function ← contract.findFunctionByName? "run"
  let calldata ← externalCalldata? "get()" [] []
  let output ←
    SolidCore.Solidity.Source.ABI.encodeValues?
      [SolidCore.Solidity.Source.Ty.uint256]
      [SolidCore.Solidity.Source.Value.word 77]
  let result ←
    SolidCore.Solidity.Source.FunctionDef.call? 64
      { contract.context with
        lowLevelCallResults :=
          [ { kind := SolidCore.Solidity.Source.LowLevelCallKind.call
              target := 0xbeef
              calldata := calldata
              value := 0
              success := true
              output := output } ] }
      function SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 0xbeef]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state [] =>
      some
        (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 7 &&
          SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 77)
  | _ => some false

def usingMathLibrary : ContractDecl :=
  { name := "Math"
    kind := ContractKind.library
    items :=
      [ (ContractItem.function
          { name := some "inc"
            visibility := some Visibility.internal_
            params := [{ name := some "self", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.binary BinaryOp.add
                      (Expr.ident "self")
                      (Expr.literal (Literal.number "1"))))) })
      , (ContractItem.function
          { name := some "mix"
            visibility := some Visibility.internal_
            params :=
              [ { name := some "self", ty := Ty.uint 256 }
              , { name := some "right", ty := Ty.uint 256 } ]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.binary BinaryOp.add
                      (Expr.binary BinaryOp.mul
                        (Expr.ident "self")
                        (Expr.literal (Literal.number "10")))
                      (Expr.ident "right")))) }) ] }

def usingMethodContract : ContractDecl :=
  { name := "UsingMethod"
    items :=
      [ ContractItem.usingDecl
          { library := { segments := ["Math"] }
            target := some (Ty.uint 256) }
      , ContractItem.function
          { name := some "run"
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call (Expr.member (Expr.ident "x") "inc")
                      []))) } ] }

def usingDirectContract : ContractDecl :=
  { name := "UsingDirect"
    items :=
      [ ContractItem.function
          { name := some "run"
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call (Expr.member (Expr.ident "Math") "inc")
                      [Arg.positional (Expr.ident "x")]))) } ] }

def usingSourceLevelContract : ContractDecl :=
  { name := "UsingSourceLevel"
    items :=
      [ ContractItem.function
          { name := some "run"
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call (Expr.member (Expr.ident "x") "inc")
                      []))) } ] }

def usingStorageContract : ContractDecl :=
  { name := "UsingStorage"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.usingDecl
          { library := { segments := ["Math"] }
            target := some (Ty.uint 256) }
      , ContractItem.function
          { name := some "bump"
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.call (Expr.member (Expr.ident "x") "inc") []))) } ] }

def usingNamedMethodContract : ContractDecl :=
  { name := "UsingNamedMethod"
    items :=
      [ ContractItem.usingDecl
          { library := { segments := ["Math"] }
            target := some (Ty.uint 256) }
      , ContractItem.function
          { name := some "run"
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call (Expr.member (Expr.ident "x") "mix")
                      [Arg.named "right"
                        (Expr.literal (Literal.number "2"))]))) } ] }

def usingNamedDirectContract : ContractDecl :=
  { name := "UsingNamedDirect"
    items :=
      [ ContractItem.function
          { name := some "run"
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.call (Expr.member (Expr.ident "Math") "mix")
                      [ Arg.named "right"
                          (Expr.literal (Literal.number "2"))
                      , Arg.named "self"
                          (Expr.literal (Literal.number "4")) ]))) } ] }

def usingLibraryUnit : SourceUnit :=
  { items :=
      [ SourceItem.contract usingMathLibrary
      , SourceItem.contract usingMethodContract
      , SourceItem.contract usingDirectContract
      , SourceItem.usingDecl
          { library := { segments := ["Math"] }
            target := some (Ty.uint 256) }
      , SourceItem.contract usingSourceLevelContract
      , SourceItem.contract usingStorageContract
      , SourceItem.contract usingNamedMethodContract
      , SourceItem.contract usingNamedDirectContract ] }

def usingLibraryMethodMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 usingLibraryUnit "UsingMethod"
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 41]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 42)
  | _ => some false

def usingLibraryDirectCallMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 usingLibraryUnit "UsingDirect"
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 11]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 12)
  | _ => some false

def usingSourceLevelMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 usingLibraryUnit "UsingSourceLevel"
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 6]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 7)
  | _ => some false

def usingStorageReceiverMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 usingLibraryUnit "UsingStorage"
      (SolidCore.Solidity.Source.CallTarget.name "bump")
      (SolidCore.Solidity.Source.State.empty.storeSlot 0 9)
      []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 10)
  | _ => some false

def usingNamedMethodMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 usingLibraryUnit "UsingNamedMethod"
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 4]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 42)
  | _ => some false

def usingNamedDirectCallMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 32 usingLibraryUnit "UsingNamedDirect"
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word value] =>
      some (SolidCore.Solidity.Source.wordEq value 42)
  | _ => some false

def usingModifierContract : ContractDecl :=
  { name := "UsingModifier"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.usingDecl
          { library := { segments := ["Math"] }
            target := some (Ty.uint 256) }
      , ContractItem.modifierDecl
          { name := "withBump"
            params := [{ name := some "start", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.block
                  [ Stmt.expr
                      (Expr.assign (Expr.ident "x") AssignOp.assign
                        (Expr.call (Expr.member (Expr.ident "start") "inc")
                          []))
                  , Stmt.modifierPlaceholder ]) }
      , ContractItem.function
          { name := some "run"
            params := [{ name := some "seed", ty := Ty.uint 256 }]
            modifiers :=
              [ { target := { segments := ["withBump"] }
                  args :=
                    [ Arg.positional
                        (Expr.call (Expr.member (Expr.ident "seed") "inc")
                          []) ] } ]
            body := some Stmt.empty } ] }

def usingModifierUnit : SourceUnit :=
  { items :=
      [ SourceItem.contract usingMathLibrary
      , SourceItem.contract usingModifierContract ] }

def usingModifierLibraryExpansionMatches : Option Bool := do
  let result ←
    SourceUnit.callContract? 64 usingModifierUnit "UsingModifier"
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 40]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 42)
  | _ => some false

def usingConstructorContract : ContractDecl :=
  { name := "UsingConstructor"
    items :=
      [ ContractItem.stateVar { name := "x", ty := Ty.uint 256 }
      , ContractItem.usingDecl
          { library := { segments := ["Math"] }
            target := some (Ty.uint 256) }
      , ContractItem.function
          { kind := FunctionKind.constructor
            params := [{ name := some "seed", ty := Ty.uint 256 }]
            body :=
              some
                (Stmt.expr
                  (Expr.assign (Expr.ident "x") AssignOp.assign
                    (Expr.call (Expr.member (Expr.ident "seed") "inc")
                      []))) } ] }

def usingConstructorUnit : SourceUnit :=
  { items :=
      [ SourceItem.contract usingMathLibrary
      , SourceItem.contract usingConstructorContract ] }

def usingConstructorMatches : Option Bool := do
  let result ←
    SourceUnit.constructContract? 32 usingConstructorUnit
      "UsingConstructor"
      SolidCore.Solidity.Source.State.empty
      [SolidCore.Solidity.Source.Value.word 41]
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ =>
      some (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 42)
  | _ => some false

end Examples

end Executable

end L00_SourceSolidity
end Spine
end SolidCore
