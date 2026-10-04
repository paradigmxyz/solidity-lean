import SolidCore.Solidity.ABI
import SolidCore.Solidity.Ast

namespace SolidCore.Solidity.Executable

abbrev CoreTy := SolidCore.Solidity.Source.Ty
abbrev CoreValue := SolidCore.Solidity.Source.Value
abbrev CoreValueCleanup := SolidCore.Solidity.Source.ValueCleanup
abbrev CoreAbiCleanup := SolidCore.Solidity.Source.AbiCleanup
abbrev CoreExpr := SolidCore.Solidity.Source.Expr
abbrev CoreLValue := SolidCore.Solidity.Source.LValue
abbrev CoreTupleTarget := SolidCore.Solidity.Source.TupleTarget
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

/-- Solidity permits magic namespaces and global builtin functions to appear
    as discarded, bare expression statements (`msg;`, `keccak256;`, `addmod;`).
    Referencing these symbols has no runtime effect. -/
def strayBuiltinIdentAllowed (name : Name) : Bool :=
  name == "msg" || name == "block" || name == "tx" || name == "super" ||
    name == "gasleft" || name == "blockhash" || name == "blobhash" ||
    name == "addmod" || name == "mulmod" ||
    name == "keccak256" || name == "sha256" || name == "ripemd160" ||
    name == "ecrecover" || name == "erc7201" ||
    name == "assert" || name == "require" || name == "revert" ||
    name == "selfdestruct"
abbrev CoreStorageLayout := SolidCore.Solidity.Source.StorageLayout
abbrev CoreEventDecl := SolidCore.Solidity.Source.EventDecl
abbrev CoreErrorDecl := SolidCore.Solidity.Source.ErrorDecl
abbrev CoreLowLevelCallKind := SolidCore.Solidity.Source.LowLevelCallKind
abbrev CoreLowLevelCallResult :=
  SolidCore.Solidity.Source.LowLevelCallResult
abbrev SourceModifierDecl :=
  _root_.SolidCore.Solidity.ModifierDecl
abbrev SourceModifierInvocation :=
  _root_.SolidCore.Solidity.ModifierInvocation

def pathLast? (path : Path) : Option Name :=
  path.segments.reverse.head?

def Path.matchesNominal (lhs rhs : Path) : Bool :=
  lhs.segments == rhs.segments ||
    ((lhs.segments.length == 1 || rhs.segments.length == 1) &&
      pathLast? lhs == pathLast? rhs)

def pathInitLast? (path : Path) : Option (Path × Name) :=
  let rec go : List Name -> Option (List Name × Name)
    | [] => none
    | [last] => some ([], last)
    | head :: tail => do
        let (init, last) ← go tail
        some (head :: init, last)
  match go path.segments with
  | some (init, last) => some ({ segments := init }, last)
  | none => none

def StateMutability.externalFunctionCallKind :
    StateMutability -> CoreLowLevelCallKind
  | StateMutability.pure | StateMutability.view =>
      SolidCore.Solidity.Source.LowLevelCallKind.staticcall
  | StateMutability.nonpayable | StateMutability.payable =>
      SolidCore.Solidity.Source.LowLevelCallKind.call

def StateMutability.canImplicitlyConvertFunction
    (actual expected : StateMutability) : Bool :=
  if actual == expected then
    true
  else
    match actual, expected with
    | StateMutability.pure, StateMutability.view => true
    | StateMutability.pure, StateMutability.nonpayable => true
    | StateMutability.view, StateMutability.nonpayable => true
    | StateMutability.payable, StateMutability.nonpayable => true
    | _, _ => false

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

def dropCharPrefix? : List Char -> List Char -> Option (List Char)
  | [], rest => some rest
  | _ :: _, [] => none
  | prefixHead :: prefixTail, textHead :: textTail =>
      if prefixHead == textHead then
        dropCharPrefix? prefixTail textTail
      else
        none

def dropStringPrefix? (needle text : String) : Option String := do
  let rest ← dropCharPrefix? needle.toList text.toList
  some (String.ofList rest)

def immutableNameTag (name : Name) : Name :=
  "__immutable:" ++ name

def immutableNameUntag? (name : Name) : Option Name :=
  dropStringPrefix? "__immutable:" name

def stateNameAliasPrefix : Name :=
  "__solidcore_state_alias:"

def stateNameAliasEntry (source target : Name) : Name :=
  stateNameAliasPrefix ++ source ++ ":" ++ target

def stateNameAliasTarget? (source entry : Name) : Option Name :=
  dropStringPrefix? (stateNameAliasPrefix ++ source ++ ":") entry

def stateNameRuntimeKey? (name : Name) : List Name -> Option Name
  | [] => none
  | candidate :: rest =>
      if candidate == name then
        some name
      else
        match stateNameAliasTarget? name candidate with
        | some target => some target
        | none => stateNameRuntimeKey? name rest

def stateNameIsStorage (name : Name) (stateNames : List Name) : Bool :=
  (stateNameRuntimeKey? name stateNames).isSome

def stateNameIsImmutable (name : Name) (stateNames : List Name) : Bool :=
  match stateNameRuntimeKey? (immutableNameTag name) stateNames with
  | some tagged => immutableNameUntag? tagged |>.isSome
  | none => false

def stateNameImmutableKey? (name : Name) (stateNames : List Name) :
    Option Name := do
  let tagged ← stateNameRuntimeKey? (immutableNameTag name) stateNames
  immutableNameUntag? tagged

def stateNamesFrom (storageVars immutableVars : List StateVarDecl) :
    List Name :=
  storageVars.map StateVarDecl.name ++
    immutableVars.map (fun decl => immutableNameTag decl.name)

/-- Whether a state-name list entry is shadowed by a locally-bound name (a
    function parameter or named return): solc resolves a bare identifier to the
    NEAREST declaration, so within the function body such a name is the LOCAL,
    never the same-named storage/immutable state variable. Matches against the
    plain runtime key, an aliased key, and the immutable-tagged key. -/
def stateNameShadowedByBound (bound : List Name) (candidate : Name) : Bool :=
  bound.any (fun b =>
    (stateNameRuntimeKey? b [candidate]).isSome ||
    (stateNameRuntimeKey? (immutableNameTag b) [candidate]).isSome)

/-- Drop from a state-name list every entry shadowed by a locally-bound name, so
    a shadowed identifier lowers as the local (param/named return) instead of the
    state variable (param-shadows-statevar soundness fix). -/
def stateNamesExcludingBound (bound : List Name) (stateNames : List Name) :
    List Name :=
  stateNames.filter (fun candidate => !stateNameShadowedByBound bound candidate)

abbrev ConstantEnv := List (Name × Ty × Expr)

def ConstantEnv.lookup? (env : ConstantEnv) (name : Name) : Option (Ty × Expr) :=
  match env with
  | [] => none
  | (candidate, ty, expr) :: rest =>
      if candidate == name then
        some (ty, expr)
      else
        ConstantEnv.lookup? rest name

/-- Remove constants hidden by bindings in the current lexical scope. -/
def ConstantEnv.withoutNames (env : ConstantEnv) (names : List Name) : ConstantEnv :=
  env.filter (fun entry => !names.contains entry.1)

def VarBindings.boundNames (bindings : List VarBinding) : List Name :=
  bindings.filterMap (fun binding => binding.name)

def Parameters.constantShadowNames (params : List Parameter) : List Name :=
  params.filterMap (fun param => param.name)

/-- A state/file constant keeps its declared integer type at each use.  A raw
    syntactic substitution would turn `uint constant a = 12` back into an
    untyped rational literal, making `(a / 10) * 10` fold as `(12/10)*10 = 12`
    instead of performing `uint256` division and yielding `10`.  The always-true
    conditional is a pure lowering barrier: both branches are the same explicit
    conversion, while the shape prevents the untyped rational folder from
    looking through the declaration's type. -/
def Expr.constantUse (ty : Ty) (replacement : Expr) : Expr :=
  match ty with
  | Ty.uint _ | Ty.int _ =>
      let typed := Expr.call (Expr.typeName ty) [Arg.positional replacement]
      Expr.ternary (Expr.literal (Literal.bool true)) typed typed
  | _ => replacement

/-- Synthetic `ConstantEnv` key for a constant read through a type name
    (`Base.K`, `L.LK`). A `.`-joined path can never collide with a real Solidity
    identifier, so qualified entries coexist with the ordinary bare-name ones. -/
def qualifiedConstantKey (path : Path) (member : Name) : Name :=
  String.intercalate "." (path.segments ++ [member])

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
          | some (ty, replacement) => Expr.constantUse ty (inline replacement)
          | none => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member (Expr.typeName (Ty.user path)) member =>
          -- Qualified constant read (`Base.K`, `L.LK`): inline the constant's
          -- value exactly like the bare-identifier form, keyed by the joined
          -- type path. A qualified state-variable read (`Base.v`) has no
          -- constant entry and is left for storage lowering.
          match ConstantEnv.lookup? constants (qualifiedConstantKey path member) with
          | some (ty, replacement) => Expr.constantUse ty (inline replacement)
          | none => Expr.member (Expr.typeName (Ty.user path)) member
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
      | Stmt.block body =>
          Stmt.block (Stmts.inlineConstantsFuel fuel constants body)
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
          let loopConstants :=
            match init with
            | some (Stmt.varDecl bindings _) =>
                constants.withoutNames (VarBindings.boundNames bindings)
            | _ => constants
          let inlineLoopExpr := Expr.inlineConstantsFuel fuel loopConstants
          let inlineLoopStmt := Stmt.inlineConstantsFuel fuel loopConstants
          Stmt.forLoop (init.map inlineStmt) (cond.map inlineLoopExpr)
            (post.map inlineLoopExpr) (inlineLoopStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch (inlineExpr expr) (clauses.map inlineClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          let successConstants :=
            constants.withoutNames (Parameters.constantShadowNames returns)
          Stmt.tryCatchReturns (inlineExpr expr) returns
            (Stmt.inlineConstantsFuel fuel successConstants success)
            (clauses.map inlineClause)
      | Stmt.emitEvent expr => Stmt.emitEvent (inlineExpr expr)
      | Stmt.revertCall expr => Stmt.revertCall (inlineExpr expr)
      | Stmt.returnValues expr? => Stmt.returnValues (expr?.map inlineExpr)
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (inlineStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

/-- Rewrite a statement list in source order. A local declaration shadows a
    constant only for the following statements in the same lexical block; the
    filtered environment is deliberately not returned to the enclosing block. -/
def Stmts.inlineConstantsFuel : Nat -> ConstantEnv -> List Stmt -> List Stmt
  | 0, _, stmts => stmts
  | _, _, [] => []
  | fuel + 1, constants, stmt :: rest =>
      let stmt' := Stmt.inlineConstantsFuel fuel constants stmt
      let constants' :=
        match stmt with
        | Stmt.varDecl bindings _ =>
            constants.withoutNames (VarBindings.boundNames bindings)
        | _ => constants
      stmt' :: Stmts.inlineConstantsFuel fuel constants' rest

def CatchClause.inlineConstantsFuel :
    Nat -> ConstantEnv -> CatchClause -> CatchClause
  | 0, _, clause => clause
  | fuel + 1, constants, clause =>
      match clause with
      | CatchClause.clause name params body =>
          let clauseConstants :=
            constants.withoutNames (Parameters.constantShadowNames params)
          CatchClause.clause name params
            (Stmt.inlineConstantsFuel fuel clauseConstants body)

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
  { specifier with args := specifier.args.map (Arg.inlineConstants constants) }

def FunctionDecl.inlineConstants (constants : ConstantEnv)
    (decl : FunctionDecl) : FunctionDecl :=
  let shadowNames :=
    Parameters.constantShadowNames decl.params ++
      Parameters.constantShadowNames decl.returns
  let constants := constants.withoutNames shadowNames
  { decl with
    modifiers := decl.modifiers.map
      (ModifierInvocation.inlineConstants constants)
    body := decl.body.map (Stmt.inlineConstants constants) }

def ModifierDecl.inlineConstants (constants : ConstantEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  let constants :=
    constants.withoutNames (Parameters.constantShadowNames decl.params)
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
      | Expr.member (Expr.ident "super") member =>
          Expr.ident (superHelperName contractName member)
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

def Expr.rewriteBaseCallsFuel (baseNames stateNames : List Name) :
    Nat -> Expr -> Expr
  | 0, expr => expr
  | fuel + 1, expr =>
      let rewrite := Expr.rewriteBaseCallsFuel baseNames stateNames fuel
      let rewriteArg := Arg.rewriteBaseCallsFuel baseNames stateNames fuel
      let rewriteOption := CallOption.rewriteBaseCallsFuel baseNames stateNames fuel
      let rewriteTupleItem := TupleItem.rewriteBaseCallsFuel baseNames stateNames fuel
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
      | Expr.call (Expr.member (Expr.typeName (Ty.user path)) member) args =>
          -- The solc importer renders an explicit base-qualified call `Base.f()`
          -- with the base contract as `Expr.typeName (Ty.user path)` rather than
          -- `Expr.ident`.  When the single-segment path names a base contract in
          -- the linearization, route it to the same static base helper so the
          -- override is bypassed; otherwise leave it untouched.
          match path.segments with
          | [baseName] =>
              if nameIn baseName baseNames && nameIn member stateNames then
                -- A type-qualified call can target a function-typed STATE
                -- variable (`C.x()`) as well as a declared function.  State
                -- access is still the ordinary unqualified storage read; only
                -- declared functions have generated static base helpers.
                Expr.call (Expr.ident member) (args.map rewriteArg)
              else if nameIn baseName baseNames then
                Expr.call (Expr.ident (baseHelperName baseName member))
                  (args.map rewriteArg)
              else
                Expr.call (Expr.member (Expr.typeName (Ty.user path)) member)
                  (args.map rewriteArg)
          | _ =>
              Expr.call (Expr.member (Expr.typeName (Ty.user path)) member)
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

def Arg.rewriteBaseCallsFuel (baseNames stateNames : List Name) :
    Nat -> Arg -> Arg
  | 0, arg => arg
  | fuel + 1, arg =>
      let rewrite := Expr.rewriteBaseCallsFuel baseNames stateNames fuel
      match arg with
      | Arg.positional expr => Arg.positional (rewrite expr)
      | Arg.named name expr => Arg.named name (rewrite expr)

def CallOption.rewriteBaseCallsFuel (baseNames stateNames : List Name) :
    Nat -> CallOption -> CallOption
  | 0, option => option
  | fuel + 1, option =>
      let rewrite := Expr.rewriteBaseCallsFuel baseNames stateNames fuel
      match option with
      | CallOption.named name expr => CallOption.named name (rewrite expr)

def TupleItem.rewriteBaseCallsFuel (baseNames stateNames : List Name) :
    Nat -> TupleItem -> TupleItem
  | 0, item => item
  | fuel + 1, item =>
      let rewrite := Expr.rewriteBaseCallsFuel baseNames stateNames fuel
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (rewrite expr)

end

def Expr.rewriteBaseCalls (baseNames stateNames : List Name) (expr : Expr) : Expr :=
  Expr.rewriteBaseCallsFuel baseNames stateNames defaultInlineConstantsFuel expr

def Arg.rewriteBaseCalls (baseNames stateNames : List Name) (arg : Arg) : Arg :=
  Arg.rewriteBaseCallsFuel baseNames stateNames defaultInlineConstantsFuel arg

def CallOption.rewriteBaseCalls (baseNames stateNames : List Name)
    (option : CallOption) : CallOption :=
  CallOption.rewriteBaseCallsFuel baseNames stateNames defaultInlineConstantsFuel option

def TupleItem.rewriteBaseCalls (baseNames stateNames : List Name)
    (item : TupleItem) : TupleItem :=
  TupleItem.rewriteBaseCallsFuel baseNames stateNames defaultInlineConstantsFuel item

mutual

def Stmt.rewriteBaseCallsFuel (baseNames stateNames : List Name) :
    Nat -> Stmt -> Stmt
  | 0, stmt => stmt
  | fuel + 1, stmt =>
      let rewriteExpr := Expr.rewriteBaseCallsFuel baseNames stateNames fuel
      let rewriteStmt := Stmt.rewriteBaseCallsFuel baseNames stateNames fuel
      let rewriteClause := CatchClause.rewriteBaseCallsFuel baseNames stateNames fuel
      let rewriteArg : Arg -> Arg
        | Arg.positional e => Arg.positional (rewriteExpr e)
        | Arg.named n e => Arg.named n (rewriteExpr e)
      -- QUAL-CALLEE (#74/#77): a base-/self-qualified event or custom-error
      -- invocation `Base.E(a)` / `C.Err(a)` shares the surface syntax of an
      -- explicit base FUNCTION call `Base.f(a)`, which `Expr.rewriteBaseCalls`
      -- mangles into the static base helper `__base_Base_f`. Events and errors
      -- must NOT be mangled — the qualifier only selects the declaration, whose
      -- UNQUALIFIED name keys the flattened event/error table (own + inherited).
      -- So for the emit/revert/require callee, rewrite only the ARGUMENTS (which
      -- may themselves contain base calls) and keep the member callee intact.
      let rewriteEventErrorCall (callExpr : Expr) : Expr :=
        match callExpr with
        | Expr.call (Expr.member target member) args =>
            Expr.call (Expr.member (rewriteExpr target) member)
              (args.map rewriteArg)
        | other => rewriteExpr other
      match stmt with
      | Stmt.empty => Stmt.empty
      | Stmt.block body => Stmt.block (body.map rewriteStmt)
      | Stmt.varDecl bindings init =>
          Stmt.varDecl bindings (init.map rewriteExpr)
      -- QUAL-CALLEE (#77), require form: keep the base-/self-qualified
      -- custom-error callee unmangled (see `rewriteEventErrorCall`). Restricted
      -- to a user-type qualifier (`Ty.user`, i.e. a contract/library) so a
      -- builtin member reason such as `require(cond, string.concat(a, b))`
      -- keeps its ordinary path.
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [Arg.positional cond,
             Arg.positional
               (Expr.call
                 (Expr.member (Expr.typeName (Ty.user path)) name) errorArgs)]) =>
          Stmt.expr
            (Expr.call (Expr.ident "require")
              [ Arg.positional (rewriteExpr cond)
              , Arg.positional
                  (Expr.call (Expr.member (Expr.typeName (Ty.user path)) name)
                    (errorArgs.map rewriteArg)) ])
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
      | Stmt.emitEvent expr => Stmt.emitEvent (rewriteEventErrorCall expr)
      | Stmt.revertCall expr => Stmt.revertCall (rewriteEventErrorCall expr)
      | Stmt.returnValues expr? => Stmt.returnValues (expr?.map rewriteExpr)
      | Stmt.break => Stmt.break
      | Stmt.continue => Stmt.continue
      | Stmt.unchecked body => Stmt.unchecked (rewriteStmt body)
      | Stmt.inlineAssembly code => Stmt.inlineAssembly code
      | Stmt.modifierPlaceholder => Stmt.modifierPlaceholder

def CatchClause.rewriteBaseCallsFuel (baseNames stateNames : List Name) :
    Nat -> CatchClause -> CatchClause
  | 0, clause => clause
  | fuel + 1, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name params
            (Stmt.rewriteBaseCallsFuel baseNames stateNames fuel body)

end

def Stmt.rewriteBaseCalls (baseNames stateNames : List Name) (stmt : Stmt) : Stmt :=
  Stmt.rewriteBaseCallsFuel baseNames stateNames defaultInlineConstantsFuel stmt

def CatchClause.rewriteBaseCalls (baseNames stateNames : List Name)
    (clause : CatchClause) : CatchClause :=
  CatchClause.rewriteBaseCallsFuel baseNames stateNames defaultInlineConstantsFuel clause

inductive DispatchCallRewriteKind where
  | ordinary
  | superCall
  | explicitBaseCall
  deriving Repr, BEq

def Expr.dispatchCallRewriteKind (baseNames : List Name) :
    Expr -> DispatchCallRewriteKind
  | Expr.call (Expr.member (Expr.ident "super") _) _ =>
      DispatchCallRewriteKind.superCall
  | Expr.callWithOptions (Expr.member (Expr.ident "super") _) _ _ =>
      DispatchCallRewriteKind.superCall
  | Expr.call (Expr.member (Expr.ident baseName) _) _ =>
      if nameIn baseName baseNames then
        DispatchCallRewriteKind.explicitBaseCall
      else
        DispatchCallRewriteKind.ordinary
  | Expr.callWithOptions (Expr.member (Expr.ident baseName) _) _ _ =>
      if nameIn baseName baseNames then
        DispatchCallRewriteKind.explicitBaseCall
      else
        DispatchCallRewriteKind.ordinary
  | _ => DispatchCallRewriteKind.ordinary

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

abbrev UserTypeEnv := List (Path × Ty)

abbrev EnumEnv := List (Path × EnumDecl)

abbrev StructEnv := List (Path × StructDecl)

def pathOfName (name : Name) : Path :=
  { segments := [name] }

def qualifiedPath (scope name : Name) : Path :=
  { segments := [scope, name] }

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

/-- Remove the nearest binding for `name`, exposing an older binding with the
    same name when one exists.  Modifier bodies are declared outside the
    modified function's parameter scope, so this is used to peel the function
    parameter/return binding while retaining the underlying state binding. -/
def TypeEnv.dropFirst (env : TypeEnv) (name : Name) : TypeEnv :=
  match env with
  | [] => []
  | entry@(candidate, _) :: rest =>
      if candidate == name then rest else entry :: TypeEnv.dropFirst rest name

def TypeEnv.dropFirstNames (env : TypeEnv) (names : List Name) : TypeEnv :=
  names.foldl (fun current name => TypeEnv.dropFirst current name) env

/-- SHADOW-LOCAL (soundness): the names a local variable declaration has SHADOWED
    in the current scope. As the lowering threads `env`, every `varDecl` PREPENDS
    its binding, so a name a nearer local now owns appears ≥2× — once as the
    shadowing local and once as the underlying declaration (state variable, param,
    named return, or an outer local). State-variable names are otherwise unique in
    a flattened contract, and each param/named-return/`this` occurs once, so a
    repeat marks EXACTLY a shadowed name. Dropping these from `storageNames` before
    lowering a statement makes a bare shadowed identifier lower as the local
    (`Expr.var`) instead of a storage read/write — matching solc's nearest-
    declaration resolution and C99 block scoping (the entry re-derives this from
    the CURRENT `env`, so a name reverts to the state variable once its local's
    block ends and the binding leaves `env`). -/
def TypeEnv.shadowedStateNames (env : TypeEnv) : List Name :=
  let names := env.map Prod.fst
  names.filter (fun n => (names.filter (fun m => m == n)).length ≥ 2)

def UserTypeEnv.lookup? (env : UserTypeEnv) (path : Path) :
    Option Ty :=
  match env with
  | [] => none
  | (candidate, ty) :: rest =>
      if candidate == path then
        some ty
      else
        UserTypeEnv.lookup? rest path

def UserTypeEnv.lookupName? (env : UserTypeEnv) (name : Name) :
    Option Ty :=
  UserTypeEnv.lookup? env (pathOfName name)

def UserTypeEnv.extendDecl (env : UserTypeEnv)
    (decl : UserValueTypeDecl) : UserTypeEnv :=
  (pathOfName decl.name, decl.underlying) :: env

def UserTypeEnv.extendQualifiedDecl (env : UserTypeEnv)
    (scope : Name) (decl : UserValueTypeDecl) : UserTypeEnv :=
  (qualifiedPath scope decl.name, decl.underlying) :: env

def EnumEnv.lookup? (env : EnumEnv) (path : Path) :
    Option EnumDecl :=
  match env with
  | [] => none
  | (candidate, decl) :: rest =>
      if candidate == path then
        some decl
      else
        EnumEnv.lookup? rest path

def EnumEnv.lookupName? (env : EnumEnv) (name : Name) :
    Option EnumDecl :=
  EnumEnv.lookup? env (pathOfName name)

def EnumEnv.extendDecl (env : EnumEnv) (decl : EnumDecl) : EnumEnv :=
  (pathOfName decl.name, decl) :: env

-- BUG#6: stamp the declaring scope into the stored decl so resolution can
-- produce the canonical (`Lib.Mode`) source path in the resolved `Ty.enum`.
def EnumDecl.stampScope (scope : Name) (decl : EnumDecl) : EnumDecl :=
  { decl with declScope? := some scope }

def EnumEnv.extendQualifiedDecl (env : EnumEnv)
    (scope : Name) (decl : EnumDecl) : EnumEnv :=
  (qualifiedPath scope decl.name, EnumDecl.stampScope scope decl) :: env

def StructEnv.lookup? (env : StructEnv) (path : Path) :
    Option StructDecl :=
  match env with
  | [] => none
  | (candidate, decl) :: rest =>
      if candidate == path then
        some decl
      else
        StructEnv.lookup? rest path

def StructEnv.lookupName? (env : StructEnv) (name : Name) :
    Option StructDecl :=
  StructEnv.lookup? env (pathOfName name)

def StructEnv.extendDecl (env : StructEnv) (decl : StructDecl) :
    StructEnv :=
  (pathOfName decl.name, decl) :: env

-- BUG#6: stamp the declaring scope so the library-qualified signature
-- renderer can recover the canonical (`Lib.S`) name from a written path.
def StructDecl.stampScope (scope : Name) (decl : StructDecl) : StructDecl :=
  { decl with declScope? := some scope }

def StructEnv.extendQualifiedDecl (env : StructEnv)
    (scope : Name) (decl : StructDecl) : StructEnv :=
  (qualifiedPath scope decl.name, StructDecl.stampScope scope decl) :: env

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

def abiDecodeReturnExprs (tys : List CoreTy)
    (cleanups : List CoreAbiCleanup) (dataCore : CoreExpr) :
    List CoreExpr :=
  let decoded :=
    SolidCore.Solidity.Source.Expr.abiDecode tys cleanups dataCore
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
      | Ty.struct path tys => Ty.struct path (tys.map resolve)
      | Ty.user path =>
          match UserTypeEnv.lookup? env path with
          | some underlying => resolve underlying
          | none => Ty.user path
      | Ty.functionWithLocations params paramLocations returns returnLocations
          mutability visibility =>
          Ty.functionWithLocations (params.map resolve) paramLocations
            (returns.map resolve) returnLocations mutability visibility
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
      | Expr.call (Expr.typeName ty@(Ty.user path)) args =>
          -- A user-defined value type conversion erases to its underlying
          -- integer type, including a redundant conversion around an
          -- `abi.decode` result. Preserve unresolved user paths: those can
          -- name struct constructors rather than value-type conversions.
          let castTy :=
            match UserTypeEnv.lookup? env path with
            | some _ => Ty.resolveUserTypesFuel fuel env ty
            | none => ty
          Expr.call (Expr.typeName castTy) (args.map resolveArg)
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
      | Expr.call
          (Expr.member
            (Expr.member (Expr.typeName (Ty.user parentPath)) typeName)
            member)
          [Arg.positional arg] =>
          let ty := Ty.user { segments := parentPath.segments ++ [typeName] }
          if member == "wrap" || member == "unwrap" then
            Expr.call (Expr.typeName (Ty.resolveUserTypesFuel fuel env ty))
              [Arg.positional (resolve arg)]
          else
            Expr.call
              (Expr.member
                (Expr.member (Expr.typeName (Ty.user parentPath)) typeName)
                member)
              [Arg.positional (resolve arg)]
      | Expr.call
          (Expr.member
            (Expr.member (Expr.typeName (Ty.user parentPath)) typeName)
            member)
          args =>
          Expr.call
            (Expr.member
              (Expr.member (Expr.typeName (Ty.user parentPath)) typeName)
              member)
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
    layoutBase := decl.layoutBase.map (Expr.resolveUserTypes env)
    bases :=
      decl.bases.map (fun spec =>
        { spec with args := spec.args.map (Arg.resolveUserTypes env) })
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
  | SourceItem.freeEvent decl =>
      SourceItem.freeEvent (EventDecl.resolveUserTypes env decl)
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

-- Canonical (declaring-scope-qualified) source path: `Lib.Mode` for an enum
-- declared inside contract/library `Lib`, `Mode` for a file-level enum.
def EnumDecl.canonicalPath (decl : EnumDecl) : Path :=
  match decl.declScope? with
  | some scope => qualifiedPath scope decl.name
  | none => pathOfName decl.name

def EnumDecl.toResolvedTy (decl : EnumDecl) : Ty :=
  match EnumDecl.maxValue? decl with
  | some maxValue => Ty.enum (EnumDecl.canonicalPath decl) maxValue
  | none => Ty.uint 8

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
      | Ty.struct path tys => Ty.struct path (tys.map resolve)
      | Ty.user path =>
          match EnumEnv.lookup? env path with
          | some decl => EnumDecl.toResolvedTy decl
          | none => Ty.user path
      | Ty.functionWithLocations params paramLocations returns returnLocations
          mutability visibility =>
          Ty.functionWithLocations (params.map resolve) paramLocations
            (returns.map resolve) returnLocations mutability visibility
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
                    -- #178 ENUM-MEMBER-ENCODEPACKED: keep the enum-ness of a
                    -- member literal (E.C) so downstream packing sees a 1-byte
                    -- (uint8) underlying width, mirroring the `E(x)` conversion
                    -- form. A bare number literal would pack at the full word.
                    -- `numberLiteralRat?` looks through `enumFromUInt`, so
                    -- constant contexts (e.g. `uint8(E.C)`) still fold.
                    match EnumDecl.maxValue? decl with
                    | some maxValue =>
                        Expr.enumFromUInt maxValue
                          (Expr.literal (Literal.number (toString index)))
                    | none => Expr.literal (Literal.number (toString index))
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
    layoutBase := decl.layoutBase.map (Expr.resolveEnums env)
    bases :=
      decl.bases.map (fun spec =>
        { spec with args := spec.args.map (Arg.resolveEnums env) })
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
  | SourceItem.freeEvent decl =>
      SourceItem.freeEvent (EventDecl.resolveEnums env decl)
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
      | Ty.struct path tys => Ty.struct path (tys.map resolve)
      | Ty.user path =>
          match StructEnv.lookup? env path with
          | some decl =>
              Ty.struct path (decl.fields.map (fun field => resolve field.ty))
          | none => Ty.user path
      | Ty.functionWithLocations params paramLocations returns returnLocations
          mutability visibility =>
          Ty.functionWithLocations (params.map resolve) paramLocations
            (returns.map resolve) returnLocations mutability visibility
      | other => other

end

def Ty.resolveStructs (env : StructEnv) (ty : Ty) : Ty :=
  Ty.resolveStructsFuel defaultResolveUserTypesFuel env ty

def StructDecl.toTupleTy (env : StructEnv) (decl : StructDecl) : Ty :=
  Ty.struct { segments := [decl.name] }
    (decl.fields.map (fun field => Ty.resolveStructs env field.ty))

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

def Expr.sourceTyWithEnv? (env : StructEnv) (typeEnv : TypeEnv) :
    Expr -> Option Ty
  | Expr.ident name =>
      TypeEnv.lookup? typeEnv name
  | Expr.call (Expr.typeName ty) _ =>
      some ty
  | Expr.member base member => do
      let baseTy ← Expr.sourceTyWithEnv? env typeEnv base
      let baseDecl ← Ty.structDecl? env baseTy
      let field ← StructDecl.field? baseDecl member
      some field.ty
  | Expr.index base _ => do
      let baseTy ← Expr.sourceTyWithEnv? env typeEnv base
      match baseTy with
      | Ty.array elementTy _ => some elementTy
      | Ty.mapping _ valueTy => some valueTy
      | Ty.bytes => some (Ty.bytesN 1)
      | _ => none
  | Expr.tuple items => do
      let tys ←
        mapOption
          (fun item =>
            match item with
            | TupleItem.value
                (Expr.call (Expr.typeName ty) [Arg.positional _]) =>
                some ty
            | TupleItem.value (Expr.typeName ty) => some ty
            | TupleItem.value _ => none
            | TupleItem.hole => none)
          items
      some (Ty.tuple tys)
  | Expr.ternary _ thenExpr _ =>
      Expr.sourceTyWithEnv? env typeEnv thenExpr
  | Expr.call (Expr.member base "push") [] => do
      -- PUSH-FIELD-LVALUE: the zero-arg `.push()` on a storage dynamic array
      -- returns a reference to the newly-appended element, whose type is the
      -- array's element type. Inferring it here lets the struct-member→index
      -- rewrite in `resolveStructsFuel` turn `xs.push().a` into
      -- `xs.push()[fieldIndex]`, which the lowering handles. (`.push(v)` takes an
      -- argument and returns nothing, so it is deliberately NOT matched.)
      let baseTy ← Expr.sourceTyWithEnv? env typeEnv base
      match baseTy with
      | Ty.array elementTy _ => some elementTy
      | _ => none
  | _ => none

def Expr.structDeclWithEnv? (env : StructEnv) (typeEnv : TypeEnv)
    (expr : Expr) : Option StructDecl := do
  let ty ← Expr.sourceTyWithEnv? env typeEnv expr
  Ty.structDecl? env ty

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
      | Expr.index (Expr.ident name) index =>
          -- BYTESN-IDENT-INDEX (#175/#176): indexing a `bytesN` value by a bare
          -- identifier base (local, parameter, or state variable) must route to
          -- the fixed-bytes byte-extraction path — solc returns the byte and, on
          -- an out-of-range index, Panics 0x32 (array out-of-bounds). The
          -- env-free `Expr.toCore?` ident-index arm cannot see the identifier's
          -- type, so it emitted a generic `index`/`storageIndex` that Panics
          -- 0x00 (type mismatch) at runtime. Here — where the full `TypeEnv`
          -- (state vars + params + locals) IS in scope — detect a fixed-bytes
          -- identifier and wrap it in its own no-op width cast `bytesN(name)`,
          -- so the already-correct general (non-ident) index arm lowers it to
          -- `fixedBytesIndex`. Genuine array/`bytes`/mapping identifiers keep the
          -- generic path (their `sourceTyWithEnv?` is not a fixed-bytes type).
          match Expr.sourceTyWithEnv? env typeEnv (Expr.ident name) with
          | some (Ty.bytesN size) =>
              if 0 < size && size <= 32 then
                Expr.index
                  (Expr.call (Expr.typeName (Ty.bytesN size))
                    [Arg.positional (Expr.ident name)])
                  (resolve index)
              else
                Expr.index (Expr.ident name) (resolve index)
          | some (Ty.fixedBytes size) =>
              if 0 < size && size <= 32 then
                Expr.index
                  (Expr.call (Expr.typeName (Ty.fixedBytes size))
                    [Arg.positional (Expr.ident name)])
                  (resolve index)
              else
                Expr.index (Expr.ident name) (resolve index)
          | _ => Expr.index (Expr.ident name) (resolve index)
      | Expr.index base index =>
          -- BYTESN-CONTAINER-ELEM-INDEX: a `bytesN` value produced by a
          -- CONTAINER element / struct-member load (`a[i]`, `m[k]`, `s.b` —
          -- i.e. a non-ident base, which the ident arm above already handles)
          -- is emitted as an untagged `Value.word` by the env-free load, so a
          -- subsequent index dead-ends in `typeMismatch` (Panic 0). Mirror the
          -- ident fix: where the full `TypeEnv` IS in scope, detect a
          -- fixed-bytes base and wrap it in its own no-op width cast
          -- `bytesN(base)`, so the general (non-ident) index arm lowers it to
          -- `fixedBytesIndex` (byte extract; Panic 0x32 out-of-range). The
          -- source type is computed on the UN-resolved base so the
          -- struct-member arm of `sourceTyWithEnv?` still applies (after
          -- `resolve`, `s.b` becomes an ordinal index whose type is opaque).
          -- The same representation boundary applies to every non-identifier
          -- expression that produces `bytesN`, including a ternary-selected
          -- byte (`(c ? bs[0] : bs[1])[0]`).  Type the unresolved source base
          -- and wrap any fixed-bytes result before recursive lowering.
          match Expr.sourceTyWithEnv? env typeEnv base with
          | some (Ty.bytesN size) =>
              if 0 < size && size <= 32 then
                Expr.index
                  (Expr.call (Expr.typeName (Ty.bytesN size))
                    [Arg.positional (resolve base)])
                  (resolve index)
              else
                Expr.index (resolve base) (resolve index)
          | some (Ty.fixedBytes size) =>
              if 0 < size && size <= 32 then
                Expr.index
                  (Expr.call (Expr.typeName (Ty.fixedBytes size))
                    [Arg.positional (resolve base)])
                  (resolve index)
              else
                Expr.index (resolve base) (resolve index)
          | _ => Expr.index (resolve base) (resolve index)
      | Expr.slice base start stop =>
          Expr.slice (resolve base) (start.map resolve) (stop.map resolve)
      | Expr.call (Expr.typeName (Ty.user path)) args =>
          match StructEnv.lookup? env path with
          | some decl =>
              match StructDecl.constructorArgs? decl args with
              | some fieldExprs =>
                  let typedItems :=
                    (decl.fields.zip fieldExprs).map
                      (fun pair =>
                        TupleItem.value
                          (Expr.call
                            (Expr.typeName
                              (Ty.resolveStructsFuel fuel env pair.fst.ty))
                            [Arg.positional (resolve pair.snd)]))
                  Expr.tuple typedItems
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

def Parameter.isStorageRef (param : Parameter) : Bool :=
  match param.location with
  | some DataLocation.storage => true
  | _ => false

def Parameters.storageRefFlags : List Parameter -> List Bool
  | [] => []
  | param :: rest =>
      Parameter.isStorageRef param :: Parameters.storageRefFlags rest

def Parameters.hasStorageRef : List Parameter -> Bool
  | [] => false
  | param :: rest =>
      Parameter.isStorageRef param || Parameters.hasStorageRef rest

def FunctionDecl.typeEnv (extra : TypeEnv) (decl : FunctionDecl) :
    TypeEnv :=
  let withParams := Parameters.extendTypeEnv "_arg" extra decl.params
  Parameters.extendTypeEnv "_ret" withParams decl.returns

def TypeEnv.extendThis (env : TypeEnv) (contractName? : Option Name) :
    TypeEnv :=
  match contractName? with
  | some contractName =>
      TypeEnv.extend? env (some "this")
        (some (Ty.user { segments := [contractName] }))
  | none => env

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

/-- Struct-member resolution for a contract, seeded with the state variables it
    INHERITS from its linearized base contracts (#197). `inheritedVars` come
    most-base-first, so `StateVars.extendTypeEnv` binds nearer ancestors — and
    finally the contract's own declarations — ahead of farther ones on a name
    clash (matching solc scope, where only private base variables can be
    shadowed at all). Without the seed, a field access on a BASE-declared
    storage struct (`p.a` for `P internal p;` declared in a base) never gets
    the member→fieldIndex rewrite and the contract fails to lower. -/
def ContractDecl.resolveStructsWithInheritedVars (env : StructEnv)
    (inheritedVars : List StateVarDecl) (decl : ContractDecl) : ContractDecl :=
  let stateVars :=
    decl.items.filterMap (fun item =>
      match item with
      | ContractItem.stateVar stateVar => some stateVar
      | _ => none)
  let typeEnv := StateVars.extendTypeEnv [] (inheritedVars ++ stateVars)
  { decl with
    layoutBase := decl.layoutBase.map (Expr.resolveStructs env [])
    bases :=
      decl.bases.map (fun spec =>
        { spec with args := spec.args.map (Arg.resolveStructs env []) })
    items := decl.items.map (ContractItem.resolveStructsWithTypeEnv env typeEnv) }

def ContractDecl.resolveStructs (env : StructEnv)
    (decl : ContractDecl) : ContractDecl :=
  ContractDecl.resolveStructsWithInheritedVars env [] decl

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
  | SourceItem.freeEvent decl =>
      SourceItem.freeEvent (EventDecl.resolveStructs env decl)
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
  | current :: rest =>
      if current.name == decl.name then
        rest.find? (fun candidate =>
          candidate.bases.any (fun spec =>
            match pathLast? spec.base with
            | some name => name == decl.name
            | none => false))
      else
        ContractDecl.findImmediateDerivedInOrder? rest decl

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
  | Ty.enum _ _ =>
      some SolidCore.Solidity.Source.Ty.uint256
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
  | Ty.struct _ tys => do
      let coreTys ← Ty.listToCore? tys
      some (SolidCore.Solidity.Source.Ty.tuple coreTys)
  | Ty.user _ => some SolidCore.Solidity.Source.Ty.address
  | Ty.functionWithLocations _ _ _ _ _ Visibility.external_ =>
      some SolidCore.Solidity.Source.Ty.externalFunction
  | Ty.functionWithLocations _ _ _ _ _ _ =>
      -- Stage C (boundary-completion arc): internal function pointers are
      -- first-class runtime values (dispatch IDs).
      some SolidCore.Solidity.Source.Ty.internalFunction
  | _ => none

def Ty.listToCore? : List Ty -> Option (List CoreTy)
  | [] => some []
  | ty :: rest => do
      let head ← Ty.toCore? ty
      let tail ← Ty.listToCore? rest
      some (head :: tail)

end

/-- Core types whose runtime values are MEMORY AGGREGATES (arrays / structs
    lowered to tuples). A lowering-generated temp of such a type must be
    declared with `Stmt.memoryVarDecl` (pointer alias, as solc does), never
    plain `Stmt.varDecl`: the plain form shallow-derefs its initializer and
    runs `Ty.coerceValue?`, which has no case for the `Value.memoryRef` rows
    NESTED inside an aggregate (a `uint256[][]` whose element rows are
    memory refs), so it spuriously reverts `typeMismatch` (= Panic 0) where
    solc simply copies the pointer. Scalars/bytes keep `Stmt.varDecl`
    byte-identically. -/
def CoreTy.isMemoryAggregate : CoreTy -> Bool
  | SolidCore.Solidity.Source.Ty.fixedArray _ _ => true
  | SolidCore.Solidity.Source.Ty.dynamicArray _ => true
  | SolidCore.Solidity.Source.Ty.tuple _ => true
  | _ => false

/-- Declare a lowering-generated temp: pointer-aliasing `memoryVarDecl` for
    memory aggregates (see `CoreTy.isMemoryAggregate`), plain `varDecl`
    (byte-identical to the historical lowering) otherwise. -/
def CoreTy.tempDeclStmt (ty : CoreTy) (name : Name)
    (init? : Option CoreExpr) : CoreStmt :=
  if CoreTy.isMemoryAggregate ty then
    SolidCore.Solidity.Source.Stmt.memoryVarDecl ty name init?
  else
    SolidCore.Solidity.Source.Stmt.varDecl ty name init?

mutual

def Ty.toCoreAbiCleanup? : Ty -> Option CoreAbiCleanup
  | Ty.uint bits =>
      let bits := if bits == 0 then 256 else bits
      if 0 < bits && bits <= 256 then
        some (SolidCore.Solidity.Source.AbiCleanup.uint bits)
      else
        none
  | Ty.int bits =>
      let bits := if bits == 0 then 256 else bits
      if 0 < bits && bits <= 256 then
        some (SolidCore.Solidity.Source.AbiCleanup.int bits)
      else
        none
  | Ty.enum _ maxValue =>
      some (SolidCore.Solidity.Source.AbiCleanup.enum maxValue)
  | Ty.array elementTy none => do
      let elementCleanup ← Ty.toCoreAbiCleanup? elementTy
      some (SolidCore.Solidity.Source.AbiCleanup.dynamicArray elementCleanup)
  | Ty.array elementTy (some size) => do
      let elementCleanup ← Ty.toCoreAbiCleanup? elementTy
      some
        (SolidCore.Solidity.Source.AbiCleanup.fixedArray
          size elementCleanup)
  | Ty.tuple tys
  | Ty.struct _ tys => do
      let cleanups ← Tys.toCoreAbiCleanups? tys
      some (SolidCore.Solidity.Source.AbiCleanup.tuple cleanups)
  | Ty.mapping _ _
  | Ty.fixed _ _
  | Ty.ufixed _ _ => none
  | _ => some SolidCore.Solidity.Source.AbiCleanup.none

def Tys.toCoreAbiCleanups? : List Ty -> Option (List CoreAbiCleanup)
  | [] => some []
  | ty :: rest => do
      let head ← Ty.toCoreAbiCleanup? ty
      let tail ← Tys.toCoreAbiCleanups? rest
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
  | Ty.fixed bits decimals =>
      if Ty.validFixedPointShape bits decimals then
        some SolidCore.Solidity.Source.Ty.int256
      else
        none
  | Ty.ufixed bits decimals =>
      if Ty.validFixedPointShape bits decimals then
        some SolidCore.Solidity.Source.Ty.uint256
      else
        none
  | Ty.enum _ _ =>
      some SolidCore.Solidity.Source.Ty.uint256
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
  | Ty.functionWithLocations _ _ _ _ _ Visibility.external_ =>
      some SolidCore.Solidity.Source.Ty.externalFunction
  | Ty.functionWithLocations _ _ _ _ _ _ =>
      some SolidCore.Solidity.Source.Ty.internalFunction
  -- AGG2: a contract/interface type is a 20-byte address value in storage
  -- (`ContractType::storageBytes() = 20`, Types.h:978; packed like an address by
  -- `StorageOffsets::computeOffsets`). By storage-lowering time every UDVT / enum
  -- / struct `Ty.user` has been resolved away, so a surviving `Ty.user` is a
  -- contract path; lower it to `address` (matches the ABI lowering at :2099).
  | Ty.user _ => some SolidCore.Solidity.Source.Ty.address
  | _ => none

def Ty.storagePackedBytes? : Ty -> Option Nat
  | Ty.bool => some 1
  | Ty.address _ => some 20
  | Ty.uint bits =>
      let bits := if bits == 0 then 256 else bits
      if 0 < bits && bits <= 256 && bits % 8 == 0 then
        some (bits / 8)
      else
        none
  | Ty.int bits =>
      let bits := if bits == 0 then 256 else bits
      if 0 < bits && bits <= 256 && bits % 8 == 0 then
        some (bits / 8)
      else
        none
  | Ty.fixed bits decimals
  | Ty.ufixed bits decimals =>
      if Ty.validFixedPointShape bits decimals then
        some (bits / 8)
      else
        none
  | Ty.enum _ _ => some 1
  | Ty.bytesN size =>
      if 0 < size && size <= SolidCore.Solidity.Source.wordBytes then
        some size
      else
        none
  | Ty.fixedBytes size =>
      if 0 < size && size <= SolidCore.Solidity.Source.wordBytes then
        some size
      else
        none
  | Ty.functionWithLocations _ _ _ _ _ Visibility.external_ => some 24
  -- Internal fn pointers are an 8-byte storage type (solc via-IR;
  -- docs/refs-completion-solc-research.md §2).
  | Ty.functionWithLocations _ _ _ _ _ _ => some 8
  -- AGG2: contract/interface type = 20-byte address, packs like an address
  -- (`ContractType::storageBytes() = 20`, Types.h:978). See `toCoreStorageWord?`.
  | Ty.user _ => some 20
  | _ => none

def Ty.storagePackedSigned : Ty -> Bool
  | Ty.int _ => true
  | Ty.fixed _ _ => true
  | _ => false

/-- Enum member bound for storage-layout lowering (`none` for non-enums). -/
def Ty.storageEnumMax? : Ty -> Option Nat
  | Ty.enum _ maxValue => some maxValue
  | _ => none

def Ty.toCoreMappingKey? : Ty -> Option CoreTy
  | Ty.bytes => some SolidCore.Solidity.Source.Ty.bytesCalldata
  | Ty.string => some SolidCore.Solidity.Source.Ty.bytesCalldata
  | Ty.functionWithLocations _ _ _ _ _ _ => none
  | ty => Ty.toCoreStorageWord? ty

structure StorageLayoutPackingCursor where
  slot : Nat
  offset : Nat := 0
  deriving Repr

def StorageLayoutPackingCursor.align
    (cursor : StorageLayoutPackingCursor) :
    StorageLayoutPackingCursor :=
  if cursor.offset == 0 then cursor
  else { slot := cursor.slot + 1, offset := 0 }

def CoreStorageLayout.placeInPackedCursor
    (cursor : StorageLayoutPackingCursor) :
    CoreStorageLayout -> CoreStorageLayout × StorageLayoutPackingCursor
  | SolidCore.Solidity.Source.StorageLayout.packedScalar
      _ widthBytes signed ty =>
      let fits :=
        cursor.offset + widthBytes <= SolidCore.Solidity.Source.wordBytes
      let slot := if fits then cursor.slot else cursor.slot + 1
      let offset := if fits then cursor.offset else 0
      let nextOffset := offset + widthBytes
      let next :=
        if nextOffset == SolidCore.Solidity.Source.wordBytes then
          { slot := slot + 1, offset := 0 }
        else
          { slot := slot, offset := nextOffset }
      ( SolidCore.Solidity.Source.StorageLayout.packedScalar
          offset widthBytes signed ty
      , next )
  | layout =>
      let aligned := cursor.align
      let span :=
        max 1 (SolidCore.Solidity.Source.StorageLayout.slotSpan layout)
      (layout, { slot := aligned.slot + span, offset := 0 })

mutual

def Ty.toCoreStorageLayout? : Ty -> Option CoreStorageLayout
  | Ty.bytes => some SolidCore.Solidity.Source.StorageLayout.bytes
  | Ty.string => some SolidCore.Solidity.Source.StorageLayout.string
  | Ty.tuple tys => do
      let fields ← Tys.toCorePackedStorageLayouts? tys
      some (SolidCore.Solidity.Source.StorageLayout.struct fields)
  | Ty.struct _ tys => do
      let fields ← Tys.toCorePackedStorageLayouts? tys
      some (SolidCore.Solidity.Source.StorageLayout.struct fields)
  | Ty.array elementTy none => do
      let element ← Ty.toCoreStorageArrayElementLayout? elementTy
      some (SolidCore.Solidity.Source.StorageLayout.dynamicArray element)
  | Ty.array elementTy (some size) => do
      let element ← Ty.toCoreStorageArrayElementLayout? elementTy
      some (SolidCore.Solidity.Source.StorageLayout.fixedArray size element)
  | Ty.mapping keyTy valueTy => do
      let key ← Ty.toCoreMappingKey? keyTy
      let value ← Ty.toCoreStorageLayout? valueTy
      -- A narrow SIGNED int mapping value occupies only its low `bits/8` bytes of
      -- the value slot; solc masks the store to that width, so the high bytes of
      -- the sign-extended word stay zero (`mv[k] = int8(-1)` writes 0xff, not
      -- 0xff..ff). The width-erased `scalar int256` from `toCoreStorageLayout?`
      -- would store the FULL sign-extended word and corrupt the slot. Standalone
      -- and struct/array-member narrow ints already mask (via the `StorageField`
      -- record / packed member layout); a bare mapping value has neither, so
      -- carry the lane width here as a `packedScalar 0 (bits/8) signed` layout
      -- (unsigned narrow ints and enums fit their low bytes already, so they need
      -- no change and keep the plain `scalar` layout).
      let value :=
        match valueTy with
        | Ty.int bits =>
            if 0 < bits && bits < 256 && bits % 8 == 0 then
              SolidCore.Solidity.Source.StorageLayout.packedScalar
                0 (bits / 8) true SolidCore.Solidity.Source.Ty.int256
            else value
        | _ => value
      some (SolidCore.Solidity.Source.StorageLayout.mapping key value)
  | Ty.enum _ maxValue =>
      -- Storage layout keeps the member bound: reads mask the lane byte and
      -- defer range validation to use sites (Panic 0x21), matching solc's
      -- `cleanup_from_storage_t_enum` / `validator_assert_t_enum` split.
      -- ABI params/returns and locals keep the erased `uint256` +
      -- `AbiCleanup.enum` lowering.
      some
        (SolidCore.Solidity.Source.StorageLayout.scalar
          (SolidCore.Solidity.Source.Ty.enumStorage maxValue))
  | ty => do
      let scalar ← Ty.toCoreStorageWord? ty
      some (SolidCore.Solidity.Source.StorageLayout.scalar scalar)

def Ty.toCoreStorageMemberLayout? (ty : Ty) :
    Option CoreStorageLayout :=
  match Ty.storageEnumMax? ty,
      Ty.storagePackedBytes? ty, Ty.toCoreStorageWord? ty with
  | some maxValue, _, _ =>
      -- Packed 1-byte enum lane, carrying the member bound (see
      -- `toCoreStorageLayout?`).
      some
        (SolidCore.Solidity.Source.StorageLayout.packedScalar 0 1 false
          (SolidCore.Solidity.Source.Ty.enumStorage maxValue))
  | none, some widthBytes, some scalar =>
      some
        (SolidCore.Solidity.Source.StorageLayout.packedScalar
          0 widthBytes (Ty.storagePackedSigned ty) scalar)
  | _, _, _ => Ty.toCoreStorageLayout? ty

/-- Array elements of at most 16 bytes pack multiple values into one slot.
    Wider elementary elements occupy a fresh full slot per element, even
    though their source type is narrower than 256 bits. In particular, solc
    stores a negative `int192` array element as a sign-extended full word;
    treating it as a 24-byte packed lane incorrectly leaves the high eight
    bytes zero. Struct fields retain the ordinary adjacent-field packing above. -/
def Ty.toCoreStorageArrayElementLayout? (ty : Ty) :
    Option CoreStorageLayout :=
  match Ty.storageEnumMax? ty,
      Ty.storagePackedBytes? ty, Ty.toCoreStorageWord? ty with
  | some maxValue, _, _ =>
      some
        (SolidCore.Solidity.Source.StorageLayout.packedScalar 0 1 false
          (SolidCore.Solidity.Source.Ty.enumStorage maxValue))
  | none, some widthBytes, some scalar =>
      if widthBytes <= SolidCore.Solidity.Source.wordBytes / 2 then
        some
          (SolidCore.Solidity.Source.StorageLayout.packedScalar
            0 widthBytes (Ty.storagePackedSigned ty) scalar)
      else
        some (SolidCore.Solidity.Source.StorageLayout.scalar scalar)
  | _, _, _ => Ty.toCoreStorageLayout? ty

def Tys.toCoreStorageLayouts? : List Ty -> Option (List CoreStorageLayout)
  | [] => some []
  | ty :: rest => do
      let head ← Ty.toCoreStorageLayout? ty
      let tail ← Tys.toCoreStorageLayouts? rest
      some (head :: tail)

def Tys.toCorePackedStorageLayoutsFrom?
    (cursor : StorageLayoutPackingCursor) :
    List Ty ->
      Option (List CoreStorageLayout × StorageLayoutPackingCursor)
  | [] => some ([], cursor)
  | ty :: rest => do
      let rawLayout ← Ty.toCoreStorageMemberLayout? ty
      let (layout, next) :=
        CoreStorageLayout.placeInPackedCursor cursor rawLayout
      let (tail, finalCursor) ←
        Tys.toCorePackedStorageLayoutsFrom? next rest
      some (layout :: tail, finalCursor)

def Tys.toCorePackedStorageLayouts? (tys : List Ty) :
    Option (List CoreStorageLayout) := do
  let (layouts, _) ←
    Tys.toCorePackedStorageLayoutsFrom?
      { slot := 0, offset := 0 } tys
  some layouts

end

def Ty.hasStorageArrayMembers : Ty -> Bool
  | Ty.array _ none => true
  | Ty.bytes => true
  | _ => false

-- SHALLOW omission (mirror of the TypeCheck copy): only a *direct* mapping or
-- *direct* (non-string/bytes) array member is omitted from a struct getter; a
-- nested struct member is returned WHOLE. Matches solc
-- `FunctionType(VariableDeclaration)` in Types.cpp.
def Ty.omittedFromStructPublicGetter? : Nat -> Ty -> Bool
  | 0, _ => false
  | _ + 1, Ty.mapping _ _ => true
  | _ + 1, Ty.array _ _ => true
  | _ + 1, _ => false

def Ty.publicGetterStructReturnFields? (fuel : Nat) :
    Nat -> List Ty -> Option (List (List Nat × Ty))
  | _, [] => some []
  | index, ty :: rest => do
      let tail ← Ty.publicGetterStructReturnFields? fuel (index + 1) rest
      if Ty.omittedFromStructPublicGetter? fuel ty then
        some tail
      else
        some (([index], ty) :: tail)

def Ty.publicGetterReturnFields? : Nat -> Ty ->
    Option (List (List Nat × Ty))
  | 0, _ => none
  | fuel + 1, Ty.tuple tys =>
      Ty.publicGetterStructReturnFields? fuel 0 tys
  | fuel + 1, Ty.struct _ tys =>
      Ty.publicGetterStructReturnFields? fuel 0 tys
  | _ + 1, ty => some [([], ty)]

def Ty.publicGetterShape? : Nat -> Ty ->
    Option (List Ty × List (List Nat × Ty))
  | 0, _ => none
  | fuel + 1, Ty.mapping keyTy valueTy => do
      let tail ← Ty.publicGetterShape? fuel valueTy
      some (keyTy :: tail.fst, tail.snd)
  | fuel + 1, Ty.array elementTy _ => do
      let tail ← Ty.publicGetterShape? fuel elementTy
      some (Ty.uint 256 :: tail.fst, tail.snd)
  | fuel + 1, ty => do
      let returns ← Ty.publicGetterReturnFields? fuel ty
      some ([], returns)

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
  | Ty.fixed bits decimals =>
      if Ty.validFixedPointShape bits decimals then
        some ("fixed" ++ toString bits ++ "x" ++ toString decimals)
      else
        none
  | Ty.ufixed bits decimals =>
      if Ty.validFixedPointShape bits decimals then
        some ("ufixed" ++ toString bits ++ "x" ++ toString decimals)
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
  | Ty.struct _ tys => do
      let elements ← Ty.listAbiCanonical? tys
      some ("(" ++ joinStringsWith "," elements ++ ")")
  | Ty.enum _ _ => some "uint8"
  | Ty.user _ => some "address"
  | Ty.functionWithLocations _ _ _ _ _ _ => some "function"
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

def BinaryOp.tempTag : BinaryOp -> String
  | BinaryOp.add => "add"
  | BinaryOp.sub => "sub"
  | BinaryOp.mul => "mul"
  | BinaryOp.div => "div"
  | BinaryOp.mod => "mod"
  | BinaryOp.exp => "exp"
  | BinaryOp.bitAnd => "bitAnd"
  | BinaryOp.bitOr => "bitOr"
  | BinaryOp.bitXor => "bitXor"
  | BinaryOp.shl => "shl"
  | BinaryOp.shr => "shr"
  | BinaryOp.sar => "sar"
  | BinaryOp.lt => "lt"
  | BinaryOp.gt => "gt"
  | BinaryOp.le => "le"
  | BinaryOp.ge => "ge"
  | BinaryOp.eq => "eq"
  | BinaryOp.ne => "ne"
  | BinaryOp.boolAnd => "boolAnd"
  | BinaryOp.boolOr => "boolOr"

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
  -- Solidity's number scanner allows an OPTIONAL '-' in a scientific-notation
  -- exponent, but NEVER a leading '+': `1e+5`, `1E+5`, `1.0e+2`, `2e+3 seconds`
  -- are all scan-time "Invalid literal value" rejects in solc 0.8.35. A leading
  -- '+' falls through to the bare-digits branch below, where the '+' is not a
  -- decimal digit and `parseSeparatedDigits?` yields `none` (reject). (#159)
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
  num : Int
  den : Nat
  deriving Repr

def NumberRat.ofNat (value : Nat) : NumberRat :=
  { num := Int.ofNat value, den := 1 }

def NumberRat.ofInt (value : Int) : NumberRat :=
  { num := value, den := 1 }

-- Build a rational from a signed numerator and a (possibly signed) denominator,
-- canonicalizing so the stored denominator is a strictly-positive `Nat`.
def NumberRat.mk? (num den : Int) : Option NumberRat :=
  if den == 0 then
    none
  else if den < 0 then
    some { num := -num, den := (-den).toNat }
  else
    some { num := num, den := den.toNat }

-- Exact signed integer value, or `none` when the reduced denominator is not 1.
def NumberRat.exactInt? (value : NumberRat) : Option Int :=
  if value.den == 0 then
    none
  else if value.num % (Int.ofNat value.den) == 0 then
    some (value.num / (Int.ofNat value.den))
  else
    none

-- Exact non-negative integer value; rejects negatives (used by unsigned and
-- bit/shift paths, matching solc's error on those operands).
def NumberRat.exactNat? (value : NumberRat) : Option Nat := do
  let i ← value.exactInt?
  if i < 0 then none else some i.toNat

-- solc constant-evaluator resource caps (`ConstantEvaluator.cpp`,
-- `libsolutil/Numeric.cpp`, `ast/Types.cpp`). solc folds constants in unbounded
-- signed rationals but rejects any operation whose operands/result would exceed
-- these bit budgets; we replicate the exact thresholds so solidity-lean rejects the
-- same programs solc does (closing the CE-6a over-accept family).
def uint32MaxNat : Nat := 4294967295          -- std::numeric_limits<uint32_t>::max()
def int32MaxNat : Nat := 2147483647           -- std::numeric_limits<int32_t>::max()
def int32MinAbsNat : Nat := 2147483648        -- |std::numeric_limits<int32_t>::min()|

-- `fitsPrecisionExp` (ConstantEvaluator.cpp:46-64): does `base ** exp` fit into
-- 4096 bits, using the most-significant-bit of the (non-negative) base.
def fitsPrecisionExp (base exp : Nat) : Bool :=
  if base == 0 then true
  else
    let msb := Nat.log2 base
    if msb == 0 then true            -- base == 1
    else if msb > 4096 then false    -- base >= 2 ^ 4096
    else exp * (msb + 1) <= 4096

-- `fitsPrecisionBaseX` (libsolutil/Numeric.cpp:25-40): does
-- `mantissa * (base ** exp)` fit into 4096 bits, where `log2OfBaseNum/den`
-- approximates log2(base). `bitsNeeded = msb(mantissa) + floor(exp*log2(base)) + 1`.
def fitsPrecisionBaseX (mantissa exp log2Num log2Den : Nat) : Bool :=
  if mantissa == 0 then true
  else
    let msb := Nat.log2 mantissa
    if msb > 4096 then false
    else
      -- floor(exp * log2(base)) via exact Nat rational arithmetic.
      let floorTerm := (exp * log2Num) / log2Den
      msb + floorTerm + 1 <= 4096

-- `fitsPrecisionBase2` (ConstantEvaluator.cpp:67-70): log2(2) = 1.
def fitsPrecisionBase2 (mantissa exp : Nat) : Bool :=
  fitsPrecisionBaseX mantissa exp 1 1

-- `fitsPrecisionBase10` (Types.cpp:65-70): log2(10) ≈ 3.3219280948873624; solc
-- uses this double, we use a 16-digit rational that agrees on the floor away from
-- the (unreachable-through-the-importer) bit-budget boundary.
def fitsPrecisionBase10 (mantissa exp : Nat) : Bool :=
  fitsPrecisionBaseX mantissa exp 33219280948873624 10000000000000000

-- 4096-bit post-operation cap (Types.cpp:1130-1132): after every binary op solc
-- reduces the rational and requires `max(msb(|num|), msb(|den|)) <= 4096`.
def NumberRat.within4096 (v : NumberRat) : Bool :=
  if v.num == 0 then true
  else
    let g := Nat.gcd v.num.natAbs v.den
    let n := if g == 0 then v.num.natAbs else v.num.natAbs / g
    let d := if g == 0 then v.den else v.den / g
    Nat.max (Nat.log2 n) (Nat.log2 d) <= 4096

-- Signed two's-complement bitwise operators over `Int` (boost's bigint `& | ^`,
-- ConstantEvaluator.cpp:80-94). Lean core lacks `Int.land`/`lor`/`xor`, so we
-- derive them from `Nat` bit ops via the two's-complement identities. For x < 0,
-- `~x = -x-1 >= 0` is the magnitude of x's complemented bits.
-- `Nat.ldiff a b = a AND (NOT b)` = clear from `a` the bits set in `b`. Lean core
-- has no `Nat.ldiff`, so we use the identity `a AND ~b = a XOR (a AND b)`.
def natLdiff (a b : Nat) : Nat := Nat.xor a (Nat.land a b)

def intBitLand (a b : Int) : Int :=
  if a ≥ 0 && b ≥ 0 then Int.ofNat (Nat.land a.toNat b.toNat)
  else if a ≥ 0 then Int.ofNat (natLdiff a.toNat (-b - 1).toNat)
  else if b ≥ 0 then Int.ofNat (natLdiff b.toNat (-a - 1).toNat)
  else -(Int.ofNat (Nat.lor (-a - 1).toNat (-b - 1).toNat)) - 1

def intBitLor (a b : Int) : Int :=
  if a ≥ 0 && b ≥ 0 then Int.ofNat (Nat.lor a.toNat b.toNat)
  else if a ≥ 0 then -(Int.ofNat (natLdiff (-b - 1).toNat a.toNat)) - 1
  else if b ≥ 0 then -(Int.ofNat (natLdiff (-a - 1).toNat b.toNat)) - 1
  else -(Int.ofNat (Nat.land (-a - 1).toNat (-b - 1).toNat)) - 1

def intBitXor (a b : Int) : Int :=
  if a ≥ 0 && b ≥ 0 then Int.ofNat (Nat.xor a.toNat b.toNat)
  else if a ≥ 0 then -(Int.ofNat (Nat.xor a.toNat (-b - 1).toNat)) - 1
  else if b ≥ 0 then -(Int.ofNat (Nat.xor (-a - 1).toNat b.toNat)) - 1
  else Int.ofNat (Nat.xor (-a - 1).toNat (-b - 1).toNat)

def decimalValueWithScaleRat? (digits : List Nat) (fractionDigits : Nat)
    (exponent? : Option (Bool × Nat)) : Option NumberRat :=
  let value := digitsToNat 10 0 digits
  match exponent? with
  | none =>
      NumberRat.mk? value (10 ^ fractionDigits)
  | some (false, exponent) =>
      -- solc rejects a literal whose base-10 exponent overflows int32 or whose
      -- scaled mantissa would exceed 4096 bits (Types.cpp:940-962). `0E...` is
      -- always zero and short-circuits before the precision check.
      if value != 0 &&
          (exponent > int32MaxNat || !(fitsPrecisionBase10 value exponent)) then
        none
      else if fractionDigits <= exponent then
        some (NumberRat.ofNat (value * (10 ^ (exponent - fractionDigits))))
      else
        NumberRat.mk? value (10 ^ (fractionDigits - exponent))
  | some (true, exponent) =>
      if value != 0 &&
          (exponent > int32MinAbsNat ||
            !(fitsPrecisionBase10 (10 ^ fractionDigits) exponent)) then
        none
      else
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
  { num := lhs.num * (Int.ofNat rhs.den) + rhs.num * (Int.ofNat lhs.den)
    den := lhs.den * rhs.den }

-- Subtraction is now total: with a signed numerator a negative result is
-- representable (this is the whole fix for the A1 over-rejects).
def NumberRat.sub (lhs rhs : NumberRat) : NumberRat :=
  { num := lhs.num * (Int.ofNat rhs.den) - rhs.num * (Int.ofNat lhs.den)
    den := lhs.den * rhs.den }

def NumberRat.mul (lhs rhs : NumberRat) : NumberRat :=
  { num := lhs.num * rhs.num
    den := lhs.den * rhs.den }

def NumberRat.scaleNat (value : NumberRat) (factor : Nat) : NumberRat :=
  { value with num := value.num * (Int.ofNat factor) }

def parseUnitNumberRat? (text : String)
    (unit : UnitDenomination) : Option NumberRat := do
  -- solc REJECTS a hex number literal combined with a unit denomination
  -- (TypeChecker.cpp:3969-3975, error 5145): `0x10 ether`, `0x2 wei`,
  -- `0x1 seconds`, … are all fatal type errors. Only an *expression* such as
  -- `0x1234 * 1 days` is allowed (that is a binary op, not a single
  -- denominated literal, and never reaches this function). The importer keeps
  -- solc's `Literal.value` verbatim, so a hex literal is detectable by its
  -- `0x`/`0X` prefix — reject rather than fold it, matching solc's boundary.
  if text.startsWith "0x" || text.startsWith "0X" then
    none
  else
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
    NumberRat.mk? (lhs.num * (Int.ofNat rhs.den)) ((Int.ofNat lhs.den) * rhs.num)

def NumberRat.mod? (lhs rhs : NumberRat) : Option NumberRat :=
  -- solc folds constant `%` over rationals (ConstantEvaluator.cpp:103-113): for
  -- fractional operands `x % y = x − trunc(x/y)·y`; the integer case is boost's
  -- truncated remainder. Both collapse to `x − trunc(x/y)·y`, which reproduces
  -- `Int.tmod` on integers (sign of the dividend) and folds `7 % 2.5 = 2`.
  if rhs.num == 0 then
    none
  else
    match lhs.div? rhs with
    | some quotient =>
        let qTrunc : Int := Int.tdiv quotient.num (Int.ofNat quotient.den)
        some (lhs.sub (rhs.mul (NumberRat.ofInt qTrunc)))
    | none => none

-- solc's `Exp` (ConstantEvaluator.cpp:114-159). The exponent must be an integer
-- (denominator 1). Bases 0, 1, −1 short-circuit *before* the size/precision
-- checks — so `0**-1 = 0` and `1**(2**100)` both fold without ever materializing
-- the exponent (closing the CE-6b non-termination hazard). Otherwise |exp| must
-- fit uint32 and `fitsPrecisionExp` must hold; a negative exponent inverts.
def NumberRat.expRat? (base exp : NumberRat) : Option NumberRat := do
  let e ← exp.exactInt?
  if e == 0 then
    some (NumberRat.ofNat 1)
  else if base.num == 0 then
    -- base == 0 (incl. the `0**-1 = 0` quirk): solc returns `_left`.
    some (NumberRat.ofInt 0)
  else if base.num == Int.ofNat base.den then
    -- base == 1
    some (NumberRat.ofNat 1)
  else if base.num == -(Int.ofNat base.den) then
    -- base == −1: result is ±1 by exponent parity.
    some (NumberRat.ofInt (if e % 2 == 0 then 1 else -1))
  else
    let absE := e.natAbs
    if absE > uint32MaxNat then
      none
    else if !(fitsPrecisionExp base.num.natAbs absE &&
        fitsPrecisionExp base.den absE) then
      none
    else
      let numP : Int := base.num ^ absE
      let denP : Nat := base.den ^ absE
      if e ≥ 0 then
        some { num := numP, den := denP }
      else
        -- invert: solc `makeRational(denominator, numerator)`.
        NumberRat.mk? (Int.ofNat denP) numP

-- Bitwise ops fold over the signed numerators (ConstantEvaluator.cpp:80-94); they
-- reject fractional operands. Negative operands are handled via two's complement,
-- so `-4 | 1 = -3` and `~5 & 0xFF = 250` fold correctly.
def NumberRat.bitAnd? (lhs rhs : NumberRat) : Option NumberRat := do
  let l ← lhs.exactInt?
  let r ← rhs.exactInt?
  some (NumberRat.ofInt (intBitLand l r))

def NumberRat.bitOr? (lhs rhs : NumberRat) : Option NumberRat := do
  let l ← lhs.exactInt?
  let r ← rhs.exactInt?
  some (NumberRat.ofInt (intBitLor l r))

def NumberRat.bitXor? (lhs rhs : NumberRat) : Option NumberRat := do
  let l ← lhs.exactInt?
  let r ← rhs.exactInt?
  some (NumberRat.ofInt (intBitXor l r))

-- SHL (ConstantEvaluator.cpp:161-179): non-fractional operands; rhs ∈ [0, uint32].
-- The lhs may be negative. `0 << n` short-circuits to 0 *after* the rhs bound
-- check (so `0 << 2**33` still rejects). Otherwise `fitsPrecisionBase2` guards the
-- result width.
def NumberRat.shl? (lhs rhs : NumberRat) : Option NumberRat := do
  let l ← lhs.exactInt?
  let r ← rhs.exactInt?
  if r < 0 || r > Int.ofNat uint32MaxNat then
    none
  else if l == 0 then
    some (NumberRat.ofInt 0)
  else
    let exp := r.toNat
    if fitsPrecisionBase2 l.natAbs exp then
      some (NumberRat.ofInt (l * (2 : Int) ^ exp))
    else
      none

-- SAR (ConstantEvaluator.cpp:182-213): non-fractional; rhs ∈ [0, uint32].
-- Shifting past the most-significant bit gives −1 (negative lhs) or 0. Negative
-- values round toward −∞ via `(x+1)/2^n − 1`, so `-7 >> 1 = -4` (floor), not −3.
def NumberRat.sar? (lhs rhs : NumberRat) : Option NumberRat := do
  let l ← lhs.exactInt?
  let r ← rhs.exactInt?
  if r < 0 || r > Int.ofNat uint32MaxNat then
    none
  else if l == 0 then
    some (NumberRat.ofInt 0)
  else
    let exp := r.toNat
    if exp > Nat.log2 l.natAbs then
      some (NumberRat.ofInt (if l < 0 then -1 else 0))
    else
      let p : Int := (2 : Int) ^ exp
      if l < 0 then
        some (NumberRat.ofInt (Int.tdiv (l + 1) p - 1))
      else
        some (NumberRat.ofInt (Int.tdiv l p))

-- Both denominators are strictly positive, so cross-multiplication preserves
-- ordering; comparison is over signed numerators.
def NumberRat.compareNum (lhs rhs : NumberRat) : Int × Int :=
  (lhs.num * (Int.ofNat rhs.den), rhs.num * (Int.ofNat lhs.den))

def NumberRat.lt (lhs rhs : NumberRat) : Bool :=
  let pair := NumberRat.compareNum lhs rhs
  pair.fst < pair.snd

def NumberRat.eq (lhs rhs : NumberRat) : Bool :=
  let pair := NumberRat.compareNum lhs rhs
  pair.fst == pair.snd

def NumberRat.le (lhs rhs : NumberRat) : Bool :=
  NumberRat.lt lhs rhs || NumberRat.eq lhs rhs

def BinaryOp.applyNumberRatRaw? (op : BinaryOp)
    (lhs rhs : NumberRat) : Option NumberRat :=
  match op with
  | BinaryOp.add => some (lhs.add rhs)
  | BinaryOp.sub => some (lhs.sub rhs)
  | BinaryOp.mul => some (lhs.mul rhs)
  | BinaryOp.div => lhs.div? rhs
  | BinaryOp.mod => lhs.mod? rhs
  | BinaryOp.exp => lhs.expRat? rhs
  | BinaryOp.bitAnd => lhs.bitAnd? rhs
  | BinaryOp.bitOr => lhs.bitOr? rhs
  | BinaryOp.bitXor => lhs.bitXor? rhs
  | BinaryOp.shl => lhs.shl? rhs
  | BinaryOp.shr => lhs.sar? rhs
  | BinaryOp.sar => lhs.sar? rhs
  | _ => none

-- solc enforces the 4096-bit precision cap after *every* folded binary op
-- (Types.cpp:1130-1132); we apply it to the result uniformly.
def BinaryOp.applyNumberRat? (op : BinaryOp)
    (lhs rhs : NumberRat) : Option NumberRat := do
  let result ← BinaryOp.applyNumberRatRaw? op lhs rhs
  if result.within4096 then some result else none

-- `RationalNumberType::integerType()` (Types.cpp:1218-1232): an integer constant
-- has an integer mobile type only when it fits the union of the s256/u256 ranges,
-- i.e. `−2^255 ≤ v ≤ 2^256 − 1`.
def NumberRat.integerMobile? (v : NumberRat) : Option Int := do
  let i ← v.exactInt?
  if -(2 ^ 255 : Int) ≤ i && i ≤ (2 ^ 256 - 1 : Int) then some i else none

-- solc does not fold comparisons: both operands are converted to their mobile
-- types and compared (Types.cpp:1117-1126). The comparison is well-typed only
-- when those mobile types share a common type. We reproduce that gate so solidity-lean
-- rejects the same programs: two integers both need an integer mobile type and a
-- common integer type. Two same-sign integer literals share a common integer
-- type (u256 for both-nonnegative, s256 for both-negative), so they fold; but
-- two OPPOSITE-SIGN integer literals never share a common type — solc rejects
-- them unconditionally ("cannot be applied to types int_const -1 and int_const 1"),
-- regardless of magnitude. A pair of FRACTIONAL rationals never yields a usable
-- common type in 0.8.35: each operand's mobile type is a FixedPointType, and
-- FixedPointType::binaryOperatorResult (Types.cpp:846-855) returns nullptr for a
-- comparison (differing fractional-digit counts have no common type, and the
-- same-count path is unimplemented — "Not yet implemented - FixedPointType"),
-- while non-terminating fractions have no fixed mobile type at all ("cannot be
-- applied to types rational_const ..."). Either way solc REJECTS every
-- fractional-vs-fractional literal comparison, so we do too. A mix of integer
-- and fractional likewise has no common mobile type.
def NumberRat.comparisonFoldable (lhs rhs : NumberRat) : Bool :=
  match lhs.exactInt?, rhs.exactInt? with
  | some i, some j =>
      match lhs.integerMobile?, rhs.integerMobile? with
      | some _, some _ =>
          if i ≥ 0 && j ≥ 0 then true
          else if i < 0 && j < 0 then true
          else false
      | _, _ => false
  | none, none => false
  | _, _ => false

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
  | Expr.unary UnaryOp.neg inner => do
      let value ← Expr.numberLiteralRat? inner
      some { value with num := -value.num }
  | Expr.unary UnaryOp.bitNot inner => do
      -- solc folds `~` on any integer rational (ConstantEvaluator.cpp:223-227):
      -- `~x = −x − 1`; rejects fractional operands.
      let value ← Expr.numberLiteralRat? inner
      let i ← value.exactInt?
      some (NumberRat.ofInt (-i - 1))
  | Expr.binary op lhs rhs => do
      let lhsValue ← Expr.numberLiteralRat? lhs
      let rhsValue ← Expr.numberLiteralRat? rhs
      BinaryOp.applyNumberRat? op lhsValue rhsValue
  | Expr.call (Expr.typeName _) [Arg.positional expr] =>
      Expr.numberLiteralRat? expr
  | Expr.enumFromUInt _ inner =>
      -- An enum value built from a constant ordinal is itself a constant
      -- integer (solc's ConstantEvaluator folds enum members/conversions).
      -- This keeps `uint8(E.C)` / `uint8(E(2))` foldable now that member
      -- literals carry an `enumFromUInt` wrapper (#178).
      Expr.numberLiteralRat? inner
  | _ => none

def Expr.numberLiteralBool? : Expr -> Option Bool
  | Expr.binary op lhs rhs => do
      let lhsValue ← Expr.numberLiteralRat? lhs
      let rhsValue ← Expr.numberLiteralRat? rhs
      BinaryOp.applyNumberBool? op lhsValue rhsValue
  | _ => none

end

-- Whether a comparison of two constant number-literal operands is well-typed per
-- solc's mobile-type rule. Returns `true` for any non-literal comparison (the
-- normal typed rule applies there); only a pure literal-vs-literal comparison
-- whose operands lack a common mobile type is rejected (e.g. `2**300 < 2**301`,
-- `1/2 < 1`, and every fractional-vs-fractional pair such as `0.5 < 0.25` or
-- `1/2 == 0.5`), matching solc while still folding same-sign integer pairs like
-- `1 < 2`.
def Expr.numberComparisonFoldable? (lhs rhs : Expr) : Bool :=
  match Expr.numberLiteralRat? lhs, Expr.numberLiteralRat? rhs with
  | some l, some r => NumberRat.comparisonFoldable l r
  | _, _ => true

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
      fixedBytesWordFromBytes? size (stringUtf8Bytes text)
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

/-!
RECURSIVE-STRUCT-MEM-CONSTRUCT (#160): fuel-tolerant NOMINAL equality of two
`resolveStructs`-expanded types.

`Ty.resolveStructs` inlines a `Ty.user` struct path into `Ty.struct path
<fields>` down to a fixed fuel budget. For a SELF-REFERENTIAL struct
(`struct Node { uint v; Node[] kids; }`) that expansion never terminates, so
resolution bottoms out at a fuel-dependent depth, leaving a residual
`Ty.user Node` wherever the budget ran out. The depth of that residual depends
on how much fuel remained when resolution reached the node, so the SAME Solidity
type resolved from two different starting points (the constructor-argument cast,
resolved as it descends the expression tree, vs. the declared memory-variable
type, resolved from the top of the type) yields two structurally DIFFERENT giant
trees. A raw `==` on those trees then spuriously reports the memory-struct
construction as a type mismatch and the whole contract fails to lower
(`toCoreContract? = none`), even though solc accepts and executes it.

Two expanded types denote the same Solidity type exactly when they agree
structurally with matching struct/user PATHS at every struct boundary — the
inlined field lists are redundant (fully determined by the path + struct env).
Comparing by path and STOPPING at each struct boundary is therefore both sound
and fuel-independent: a residual `Ty.user p` matches a further expanded
`Ty.struct p _`, and the comparison never descends into the cyclic fields, so it
cannot diverge on the residual depth. Non-recursive structs resolve fully (no
residual) and still compare equal, so their behaviour is unchanged.
-/
mutual

/-- Fuel-tolerant nominal equality of two `resolveStructs`-expanded types; see
    the module note above. Compares struct/user nodes by PATH and stops at each
    struct boundary, so it is fuel-independent for self-referential structs. -/
def Ty.sameNominalType : Ty -> Ty -> Bool
  | Ty.struct pa _, Ty.struct pb _ => pa == pb
  | Ty.struct pa _, Ty.user pb => pa == pb
  | Ty.user pa, Ty.struct pb _ => pa == pb
  | Ty.array ea sa, Ty.array eb sb => sa == sb && Ty.sameNominalType ea eb
  | Ty.mapping ka va, Ty.mapping kb vb =>
      Ty.sameNominalType ka kb && Ty.sameNominalType va vb
  | Ty.tuple as, Ty.tuple bs => Ty.sameNominalTypes as bs
  | a, b => a == b
termination_by a _ => (sizeOf a, 0)

def Ty.sameNominalTypes : List Ty -> List Ty -> Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.sameNominalType a b && Ty.sameNominalTypes as bs
  | _, _ => false
termination_by as _ => (sizeOf as, 1)

end

def Ty.canImplicitlyConvert (actual expected : Ty) : Bool :=
  if actual == expected then
    true
  else
    match actual, expected with
    | Ty.address true, Ty.address false => true
    | Ty.uint actualBits, Ty.uint expectedBits =>
        let actualBits := if actualBits == 0 then 256 else actualBits
        let expectedBits := if expectedBits == 0 then 256 else expectedBits
        actualBits <= expectedBits
    | Ty.int actualBits, Ty.int expectedBits =>
        let actualBits := if actualBits == 0 then 256 else actualBits
        let expectedBits := if expectedBits == 0 then 256 else expectedBits
        actualBits <= expectedBits
    | Ty.uint actualBits, Ty.int expectedBits =>
        let actualBits := if actualBits == 0 then 256 else actualBits
        let expectedBits := if expectedBits == 0 then 256 else expectedBits
        actualBits < expectedBits
    | Ty.fixed actualBits actualDecimals,
      Ty.fixed expectedBits expectedDecimals =>
        Ty.fixedPointImplicitlyConvertible true actualBits actualDecimals
          true expectedBits expectedDecimals
    | Ty.ufixed actualBits actualDecimals,
      Ty.ufixed expectedBits expectedDecimals =>
        Ty.fixedPointImplicitlyConvertible false actualBits actualDecimals
          false expectedBits expectedDecimals
    | Ty.ufixed actualBits actualDecimals,
      Ty.fixed expectedBits expectedDecimals =>
        Ty.fixedPointImplicitlyConvertible false actualBits actualDecimals
          true expectedBits expectedDecimals
    | Ty.bytesN actualSize, Ty.bytesN expectedSize =>
        actualSize <= expectedSize
    | Ty.fixedBytes actualSize, Ty.fixedBytes expectedSize =>
        actualSize <= expectedSize
    | Ty.bytesN actualSize, Ty.fixedBytes expectedSize =>
        actualSize <= expectedSize
    | Ty.fixedBytes actualSize, Ty.bytesN expectedSize =>
        actualSize <= expectedSize
    | Ty.functionWithLocations actualParams actualParamLocations actualReturns
        actualReturnLocations actualMutability actualVisibility,
      Ty.functionWithLocations expectedParams expectedParamLocations expectedReturns
        expectedReturnLocations expectedMutability expectedVisibility =>
        actualParams == expectedParams &&
          actualParamLocations == expectedParamLocations &&
          actualReturns == expectedReturns &&
          actualReturnLocations == expectedReturnLocations &&
          actualVisibility == expectedVisibility &&
          StateMutability.canImplicitlyConvertFunction
            actualMutability expectedMutability
    | Ty.tuple actualFields, Ty.struct _ expectedFields =>
        Ty.sameNominalTypes actualFields expectedFields
    | Ty.struct _ actualFields, Ty.tuple expectedFields =>
        Ty.sameNominalTypes actualFields expectedFields
    | _, _ => false

/-- Is this the type of an INTERNAL function pointer value (a dispatch id)?
    An external function pointer (`Visibility.external_`) is an address+selector
    pair and is deliberately excluded — its comparison/encoding path is
    unrelated. Used to route fn-value number literals (the shape a bare function
    name takes after `rewriteInternalFnValueIdents`) and internal-fn comparison
    operands to the `Expr.internalFunction` pointer value. -/
def Ty.isInternalFunctionValueTy : Ty -> Bool
  | Ty.functionWithLocations _ _ _ _ _ Visibility.external_ => false
  | Ty.functionWithLocations _ _ _ _ _ _ => true
  | _ => false

def Ty.commonImplicit? (left right : Ty) : Option Ty :=
  if left == right then
    some left
  else
    match left, right with
    | Ty.address _, Ty.address _ => some (Ty.address false)
    | Ty.uint leftBits, Ty.uint rightBits =>
        let leftBits := if leftBits == 0 then 256 else leftBits
        let rightBits := if rightBits == 0 then 256 else rightBits
        some (Ty.uint (max leftBits rightBits))
    | Ty.int leftBits, Ty.int rightBits =>
        let leftBits := if leftBits == 0 then 256 else leftBits
        let rightBits := if rightBits == 0 then 256 else rightBits
        some (Ty.int (max leftBits rightBits))
    | Ty.fixed leftBits leftDecimals,
      Ty.fixed rightBits rightDecimals =>
        Ty.commonFixedPoint? true leftBits leftDecimals
          true rightBits rightDecimals
    | Ty.ufixed leftBits leftDecimals,
      Ty.ufixed rightBits rightDecimals =>
        Ty.commonFixedPoint? false leftBits leftDecimals
          false rightBits rightDecimals
    | Ty.fixed leftBits leftDecimals,
      Ty.ufixed rightBits rightDecimals =>
        Ty.commonFixedPoint? true leftBits leftDecimals
          false rightBits rightDecimals
    | Ty.ufixed leftBits leftDecimals,
      Ty.fixed rightBits rightDecimals =>
        Ty.commonFixedPoint? false leftBits leftDecimals
          true rightBits rightDecimals
    | Ty.bytesN leftSize, Ty.bytesN rightSize =>
        some (Ty.bytesN (max leftSize rightSize))
    | Ty.fixedBytes leftSize, Ty.fixedBytes rightSize =>
        some (Ty.fixedBytes (max leftSize rightSize))
    | Ty.bytesN leftSize, Ty.fixedBytes rightSize =>
        some (Ty.fixedBytes (max leftSize rightSize))
    | Ty.fixedBytes leftSize, Ty.bytesN rightSize =>
        some (Ty.fixedBytes (max leftSize rightSize))
    | Ty.struct leftPath leftFields, Ty.struct rightPath rightFields =>
        if leftPath == rightPath && Ty.sameNominalTypes leftFields rightFields then
          some left
        else
          none
    | Ty.struct _ fields, Ty.tuple tupleFields =>
        if Ty.sameNominalTypes fields tupleFields then some left else none
    | Ty.tuple tupleFields, Ty.struct _ fields =>
        if Ty.sameNominalTypes tupleFields fields then some right else none
    | _, _ =>
        if Ty.canImplicitlyConvert left right then
          some right
        else if Ty.canImplicitlyConvert right left then
          some left
        else
          none

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
  | Ty.enum _ _ => some ()
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

def Ty.implicitCleanupCore? (targetTy : Ty) (expr : CoreExpr) :
    Option CoreExpr :=
  -- Left shifts truncate to the result type width with no overflow check, even
  -- inside a checked block, so a shift result must be cleaned with a truncating
  -- cast (`uintCast`/`intCast`) rather than the checked `uintCleanup`/
  -- `intCleanup` used for the overflow-checked arithmetic operators.
  let isLeftShift :=
    match expr with
    | SolidCore.Solidity.Source.Expr.binary
        SolidCore.Solidity.Source.BinaryOp.shl _ _ => true
    | _ => false
  let isBitNot :=
    match expr with
    | SolidCore.Solidity.Source.Expr.unary
        SolidCore.Solidity.Source.UnaryOp.bitNot _ => true
    | _ => false
  -- NARROW-BITWISE (F2): `~x` on a narrow `uintN` is masked by solc with
  -- `cleanup_t_uintN` (`and(not(x),2^N-1)`), NEVER a range check — even in a
  -- checked block. Routing it through the checked `uintCleanup` would panic
  -- (0x11) because `not(x)` is a full-width word. So a narrow-uint `~` cleans
  -- with the truncating `uintCast`, matching solc. (Full-width `uint256` `~`
  -- keeps the existing `uintCleanup 256`, an identity mask, to avoid churn; and
  -- `~intN` stays on the checked `intCleanup` — `~` of an `intN`-range value is
  -- already in range, so it passes and matches solc's `signextend`.)
  let isNarrowUintBitNot :=
    match expr with
    | SolidCore.Solidity.Source.Expr.unary
        SolidCore.Solidity.Source.UnaryOp.bitNot _ =>
        match targetTy with
        | Ty.uint bits => let bits := if bits == 0 then 256 else bits; bits < 256
        | _ => false
    | _ => false
  match targetTy with
  | Ty.uint bits =>
      let bits := if bits == 0 then 256 else bits
      if 0 < bits && bits <= 256 then
        if isLeftShift || isNarrowUintBitNot then
          some (SolidCore.Solidity.Source.Expr.uintCast bits expr)
        else
          some (SolidCore.Solidity.Source.Expr.uintCleanup bits expr)
      else
        none
  | Ty.int bits =>
      let bits := if bits == 0 then 256 else bits
      if 0 < bits && bits <= 256 then
        if isLeftShift then
          some (SolidCore.Solidity.Source.Expr.intCast bits expr)
        else
          some (SolidCore.Solidity.Source.Expr.intCleanup bits expr)
      else
        none
  | _ =>
      -- FB1: `bytesN` is stored right-aligned, but solc stores it left-aligned
      -- and re-cleans every `bytesN <<` result back into its byte lane
      -- (`cleanup_t_bytesN` around `shl`). Under the right-aligned convention a
      -- left shift is exactly what pushes meaningful bits *above* the low
      -- `size`-byte lane, so the result must be masked to `2^(8*size)` — i.e. a
      -- no-op `fixedBytesCast size size` (identity for `size = 32`). `>>` keeps
      -- values in-lane and needs no mask (matching solc's already-agreeing
      -- right-shift path). This top-level arm is defense-in-depth; the recursive
      -- `Expr.toCoreFixedBytesBitOp?` walk handles nested shifts and `~`.
      match Ty.fixedBytesSize? targetTy with
      | some size =>
          if isLeftShift || isBitNot then
            some (SolidCore.Solidity.Source.Expr.fixedBytesCast size size expr)
          else
            some expr
      | none => some expr

def Ty.implicitCleanupCore (targetTy : Ty) (expr : CoreExpr) :
    CoreExpr :=
  match Ty.implicitCleanupCore? targetTy expr with
  | some cleaned => cleaned
  | none => expr

def Ty.toCoreValueCleanup? : Ty -> Option CoreValueCleanup
  | Ty.uint bits =>
      let bits := if bits == 0 then 256 else bits
      if 0 < bits && bits <= 256 then
        some (SolidCore.Solidity.Source.ValueCleanup.uint bits)
      else
        none
  | Ty.int bits =>
      let bits := if bits == 0 then 256 else bits
      if 0 < bits && bits <= 256 then
        some (SolidCore.Solidity.Source.ValueCleanup.int bits)
      else
        none
  | Ty.enum _ _ =>
      some (SolidCore.Solidity.Source.ValueCleanup.uint 8)
  | Ty.bytesN size
  | Ty.fixedBytes size =>
      if 0 < size && size <= 32 then
        some (SolidCore.Solidity.Source.ValueCleanup.fixedBytes size)
      else
        none
  | _ => some SolidCore.Solidity.Source.ValueCleanup.none

-- Packed byte width for a top-level `abi.encodePacked` argument. Narrow
-- `uintN`/`intN` pack to N/8 bytes and enums to 1 byte (solc caps enums at 256
-- members, i.e. a `uint8` underlying type). `0` means "no narrow override":
-- full-word ints, `bool`, `address`, `bytesN`, `bytes`/`string`, and arrays all
-- keep their existing type-directed packing (which is already solc-correct).
def Ty.packedTopWidth : Ty -> Nat
  | Ty.uint bits =>
      if bits == 0 || bits == 256 then 0
      else if bits % 8 == 0 && bits < 256 then bits / 8 else 0
  | Ty.int bits =>
      if bits == 0 || bits == 256 then 0
      else if bits % 8 == 0 && bits < 256 then bits / 8 else 0
  | Ty.enum _ _ => 1
  | _ => 0

def Tys.packedTopWidths (tys : List Ty) : List Nat :=
  tys.map Ty.packedTopWidth

def Expr.numberLiteralNat? (expr : Expr) : Option Nat := do
  let value ← Expr.numberLiteralRat? expr
  value.exactNat?

-- Exact signed integer value of a folded constant expression (or `none` when it
-- folds to a genuine fraction). This subsumes the old syntactic
-- `negatedNumberLiteralNat?`: negatives produced by subtraction or by a nested
-- unary minus are now recognized, not just a top-level unary minus.
def Expr.numberLiteralInt? (expr : Expr) : Option Int := do
  let value ← Expr.numberLiteralRat? expr
  value.exactInt?

def Expr.untypedNumberLiteralRat? : Expr -> Option NumberRat
  | Expr.literal (Literal.number text) => parseNumberRat? text
  | Expr.literal (Literal.unitNumber text unit) =>
      parseUnitNumberRat? text unit
  | Expr.unary UnaryOp.neg inner => do
      let value ← Expr.untypedNumberLiteralRat? inner
      some { value with num := -value.num }
  | Expr.unary UnaryOp.bitNot inner => do
      let value ← Expr.untypedNumberLiteralRat? inner
      let i ← value.exactInt?
      some (NumberRat.ofInt (-i - 1))
  | Expr.binary op lhs rhs => do
      let lhsValue ← Expr.untypedNumberLiteralRat? lhs
      let rhsValue ← Expr.untypedNumberLiteralRat? rhs
      BinaryOp.applyNumberRat? op lhsValue rhsValue
  | _ => none

def Expr.untypedNumberLiteralNat? (expr : Expr) : Option Nat := do
  let value ← Expr.untypedNumberLiteralRat? expr
  value.exactNat?

def Expr.isZeroNumberLiteralExpression (expr : Expr) : Bool :=
  match Expr.untypedNumberLiteralNat? expr with
  | some value => value == 0
  | none => false

def Expr.toCoreFixedBytesLiteralAs? (ty : Ty) : Expr -> Option CoreExpr
  | Expr.literal literal => do
      let size ← Ty.fixedBytesSize? ty
      let word ← Literal.toFixedBytesWord? size literal
      some (SolidCore.Solidity.Source.Expr.word word)
  | expr => do
      -- solc `RationalNumberType::isImplicitlyConvertibleTo` (Types.cpp:1035):
      -- ANY constant rational expression that *folds to 0* is implicitly
      -- convertible to any `bytesN` (the `m_value == rational(0)` branch — it
      -- operates on the folded value, so `1-1`, `2-2`, `3*0`, `-0`, `5-5`, …).
      -- The exact-width-hex-literal branch (`m_compatibleBytesType`) stays
      -- literal-only above and is NOT extended to folded expressions. A folded
      -- 0 lowers to the zero word regardless of the `bytesN` width.
      let _size ← Ty.fixedBytesSize? ty
      let value ← Expr.untypedNumberLiteralRat? expr
      if value.num == 0 then
        some (SolidCore.Solidity.Source.Expr.word 0)
      else
        none

def Expr.isFixedBytesLiteralCandidate : Expr -> Bool
  | Expr.literal literal => Literal.isFixedBytesCandidate literal
  | _ => false

def Ty.isAddress : Ty -> Bool
  | Ty.address _ => true
  | _ => false

def addressLiteralFits (value : Nat) : Bool :=
  value < SolidCore.Solidity.Shared.External.addressModulus

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

-- A single explicit type conversion `T(e)` (`address(e)`, `uint160(e)`, …).
-- Used to distinguish a nested identity conversion (which must be lowered by
-- recursing) from a genuine bare-literal argument (which may be bailed on when
-- out of range) inside the nested-`address(...)` lowering arms.
def Expr.isConversionCall : Expr -> Bool
  | Expr.call (Expr.typeName _) [Arg.positional _] => true
  | _ => false

def Expr.toCoreAddressLiteral? : Expr -> Option CoreExpr
  | Expr.literal (Literal.address value) =>
      some
        (SolidCore.Solidity.Source.Expr.word
          (SolidCore.Solidity.Shared.Account.addressWord value))
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
  | expr => do
      -- solc `RationalNumberType::isExplicitlyConvertibleTo` (Types.cpp:1050)
      -- operates on the already-folded `m_value`: for a nonpayable `address`
      -- target it allows `m_value == 0 || (!isNegative() && !isFractional() &&
      -- integerType() && numBits() <= 160)`. Literal-ness is irrelevant, so a
      -- constant-folded arithmetic argument like `1 + 1`, `2 * 3`, or `1 - 1`
      -- (folds to 0) is convertible exactly when it folds to a non-negative
      -- integer `< 2 ^ 160`. Fractional folds (`exactInt?` = none) and negatives
      -- are rejected, matching `!isFractional()` / `!isNegative()`. The folded
      -- integer lowers to its own runtime word (`address(1 + 1)` = 2).
      let rat ← Expr.untypedNumberLiteralRat? expr
      let i ← rat.exactInt?
      if i < 0 then
        none
      else
        let value := i.toNat
        if addressLiteralFits value then
          some (SolidCore.Solidity.Source.Expr.word value)
        else
          none

def Expr.toCorePayableLiteral? : Expr -> Option CoreExpr
  | Expr.literal (Literal.address value) =>
      some
        (SolidCore.Solidity.Source.Expr.word
          (SolidCore.Solidity.Shared.Account.addressWord value))
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
  | expr =>
      if Expr.isZeroNumberLiteralExpression expr then
        some (SolidCore.Solidity.Source.Expr.word 0)
      else
        none

def Expr.isNumberLiteralExpression : Expr -> Bool
  | Expr.literal (Literal.number _) => true
  | Expr.literal (Literal.unitNumber _ _) => true
  | Expr.unary UnaryOp.neg inner => Expr.isNumberLiteralExpression inner
  | Expr.unary UnaryOp.bitNot inner => Expr.isNumberLiteralExpression inner
  | Expr.binary _ lhs rhs =>
      Expr.isNumberLiteralExpression lhs &&
        Expr.isNumberLiteralExpression rhs
  | Expr.call (Expr.typeName _) [Arg.positional expr] =>
      Expr.isNumberLiteralExpression expr
  | _ => false

/-- A *raw* integer-literal operand: a numeric literal, a negation, or an
    arithmetic combination of such — but **not** an explicit type conversion.
    solc rejects an out-of-range raw literal cast (`uint8(300)` — the operand is
    an `int_const`), yet accepts a cast whose operand is a *typed* conversion
    expression (`uint8(int8(-1))`, `uint8(uint256(0x1234))`), reinterpreting /
    truncating it exactly like a runtime cast. The fail-closed literal-cast
    guards therefore fire only on raw literals; a `Ty(...)` conversion operand
    falls through to the runtime `uintCast`/`intCast` path, whose primitives
    already match solc's mod-arithmetic and sign-extension. -/
def Expr.isRawNumberLiteralExpression : Expr -> Bool
  | Expr.literal (Literal.number _) => true
  | Expr.literal (Literal.unitNumber _ _) => true
  | Expr.unary UnaryOp.neg inner => Expr.isRawNumberLiteralExpression inner
  -- `~lit` is a raw integer-constant operand too: `uint x = ~0;` must fail closed
  -- (solc rejects int_const −1 into an unsigned type) rather than evaluate `~0`
  -- through the 256-bit runtime path (closing the CE-2b over-accept).
  | Expr.unary UnaryOp.bitNot inner => Expr.isRawNumberLiteralExpression inner
  | Expr.binary _ lhs rhs =>
      Expr.isRawNumberLiteralExpression lhs &&
        Expr.isRawNumberLiteralExpression rhs
  | _ => false

-- Unsigned fit: `0 ≤ v ≤ 2^bits − 1` (rule (2) for unsigned, plus rule (3):
-- a negative folded value fails the lower bound, matching solc's rejection of a
-- signed literal into an unsigned type).
def uintLiteralFitsInt (bits : Nat) (v : Int) : Bool :=
  0 <= v && v < (2 ^ bits : Int)

-- Signed fit: `−2^(bits−1) ≤ v ≤ 2^(bits−1) − 1`. Rules (2) and (3) fall out of
-- this single signed range test.
def intLiteralFitsInt (bits : Nat) (v : Int) : Bool :=
  -(2 ^ (bits - 1) : Int) <= v && v <= (2 ^ (bits - 1) : Int) - 1

-- Smallest `uintN` (N a multiple of 8, 8 ≤ N ≤ 256) whose range holds the
-- non-negative integer `v`; solc's `RationalNumberType::mobileType()`
-- (`Types.cpp`) for a non-negative literal.
def smallestUintBits? (v : Nat) : Option Nat :=
  (List.range 32).findSome? fun k =>
    let bits := 8 * (k + 1)
    if v < 2 ^ bits then some bits else none

-- Smallest `intN` (N a multiple of 8) whose signed range holds `v`; solc's
-- `mobileType()` for a negative literal.
def smallestIntBits? (v : Int) : Option Nat :=
  (List.range 32).findSome? fun k =>
    let bits := 8 * (k + 1)
    if intLiteralFitsInt bits v then some bits else none

-- Mobile (smallest-fitting) type of an *untyped number-literal* expression.
-- For a plain/constant-folded integer literal this is the smallest `uintN`/`intN`
-- that holds its value; for a conditional whose both branches are untyped number
-- literals it is the common (mobile) type of the branch mobile types — matching
-- solc `TypeChecker::visit(Conditional)`:
--   `commonType(trueExpr->mobileType(), falseExpr->mobileType())`.
-- Returns `none` for anything that is not a pure untyped-integer-literal shape
-- (e.g. a typed conversion branch, a non-integer rational, or an out-of-range
-- fold), so callers fall back to their existing behavior.
def Expr.untypedLiteralMobileTy? : Expr -> Option Ty
  | Expr.ternary _ thenExpr elseExpr => do
      let thenTy ← Expr.untypedLiteralMobileTy? thenExpr
      let elseTy ← Expr.untypedLiteralMobileTy? elseExpr
      Ty.commonImplicit? thenTy elseTy
  | expr =>
      -- Only a genuine *untyped number literal* (solc `RationalNumberType`) has a
      -- `mobileType()`. Use the STRICT literal folder here — NOT
      -- `numberLiteralRat?`, which folds through an explicit `T(x)` conversion
      -- (and `enumFromUInt`) and would mis-report a TYPED branch such as
      -- `bytes2(0xBBCC)` / `uint8(5)` as an untyped `uintN` literal. A typed
      -- conversion branch must yield `none` so the ternary falls back to the
      -- branches' checked types (their common implicit type), matching solc.
      match Expr.untypedNumberLiteralRat? expr with
      | some q =>
          if q.den == 1 then
            if 0 <= q.num then
              (smallestUintBits? q.num.toNat).map Ty.uint
            else
              (smallestIntBits? q.num).map Ty.int
          else
            none
      | none => none
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf <;> omega

def Expr.toCoreNumericLiteralAs? (ty : Ty) (expr : Expr) :
    Option CoreExpr := do
  let value ← Expr.numberLiteralInt? expr
  match Ty.uintBits? ty with
  | some bits =>
      if uintLiteralFitsInt bits value then
        some (SolidCore.Solidity.Source.Expr.word value.toNat)
      else
        none
  | none =>
      match Ty.intBits? ty with
      | some bits =>
          if intLiteralFitsInt bits value then
            some
              (SolidCore.Solidity.Source.Expr.intWord
                (SolidCore.Solidity.Shared.signedToWord value))
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
                  (SolidCore.Solidity.Shared.signedToWord
                    (-(Int.ofNat (2 ^ (bits - 1))))))
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
          (SolidCore.Solidity.Shared.Account.addressWord value))
  | Literal.bytes bytes => some (SolidCore.Solidity.Source.Expr.byteArray bytes)
  | Literal.hexString text => do
      let bytes ← parseHexString? text
      some (SolidCore.Solidity.Source.Expr.byteArray bytes)
  | Literal.string text =>
      some (SolidCore.Solidity.Source.Expr.byteArray
        (stringUtf8Bytes text))
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

-- The final `Bool` (`valueBeforeSalt`) records whether the `value` option was
-- written before the `salt` option in source; solc evaluates the creation
-- options in source order (DIV-CREATE-2), so the order must be preserved.  It is
-- `true` when `value` heads the remaining options (and for the value-only /
-- salt-only / empty cases, where it is unobserved).
def CallOptions.contractCreationValueSaltLoop?
    (seenValue seenSalt : Bool) :
    List CallOption -> Option (Option Expr × Option Expr × Bool)
  | [] => some (none, none, true)
  | CallOption.named name expr :: rest =>
      if name == "value" then
        if seenValue then
          none
        else
          match
            CallOptions.contractCreationValueSaltLoop?
              true seenSalt rest with
          | some (none, salt?, _) => some (some expr, salt?, true)
          | _ => none
      else if name == "salt" then
        if seenSalt then
          none
        else
          match
            CallOptions.contractCreationValueSaltLoop?
              seenValue true rest with
          | some (value?, none, _) => some (value?, some expr, false)
          | _ => none
      else
        none

def CallOptions.contractCreationValueSalt? :
    List CallOption -> Option (Option Expr × Option Expr × Bool) :=
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
  | Expr.typeName Ty.bytes, "concat" => true
  | Expr.typeName Ty.string, "concat" => true
  | _, _ => false

def generatedLibraryAddressPrefix : String :=
  "__solidcore_library_address_"

def generatedLibraryAddressIdent (libraryName : Name) : Name :=
  generatedLibraryAddressPrefix ++ libraryName

def generatedLibraryAddressName? (name : Name) : Option Name :=
  dropStringPrefix? generatedLibraryAddressPrefix name

def sourceIdentCore (storageNames : List Name) (name : Name) : CoreExpr :=
  match generatedLibraryAddressName? name with
  | some libraryName =>
      SolidCore.Solidity.Source.Expr.contractAddress libraryName
  | none =>
      if name == "this" then
        SolidCore.Solidity.Source.Expr.self
      else
        match stateNameRuntimeKey? name storageNames with
        -- Bare state-variable identifier: a REFERENCE (materialized by the
        -- storage value-use normalizer at value-use boundaries), NOT the
        -- deliberate header-word read `.length` lowers to.
        | some key => SolidCore.Solidity.Source.Expr.storageIdent key
        | none =>
            match stateNameImmutableKey? name storageNames with
            | some key => SolidCore.Solidity.Source.Expr.immutable key
            | none => SolidCore.Solidity.Source.Expr.var name

def externalFunctionSignature? (name : Name) (argTys : List Ty) :
    Option String := do
  let canonicals ← Ty.listAbiCanonical? argTys
  some (name ++ "(" ++ joinStringsWith "," canonicals ++ ")")

def dataLocationIsStorage : Option DataLocation -> Bool
  | some DataLocation.storage => true
  | _ => false

/-- The ABI-signature rendering of a parameter type honouring its source data
    location. solc includes ` storage` (with a leading space) in the external
    signature ONLY for `storage`-pointer parameters — memory/calldata locations
    are omitted. This is the public/external LIBRARY boundary: a public library
    `function f(uint256[] storage self, ...)` has selector
    `f(uint256[] storage,...)`. -/
def Ty.abiCanonicalWithLocation? (ty : Ty) (loc : Option DataLocation) :
    Option String := do
  let base ← Ty.abiCanonical? ty
  if dataLocationIsStorage loc then
    some (base ++ " storage")
  else
    some base

def Tys.listAbiCanonicalWithLocations? :
    List Ty -> List (Option DataLocation) -> Option (List String)
  | [], _ => some []
  | ty :: tys, locs => do
      let head ← Ty.abiCanonicalWithLocation? ty (locs.headD none)
      let tail ← Tys.listAbiCanonicalWithLocations? tys locs.tail
      some (head :: tail)

def externalFunctionSignatureWithLocations? (name : Name) (argTys : List Ty)
    (locations : List (Option DataLocation)) : Option String := do
  let canonicals ← Tys.listAbiCanonicalWithLocations? argTys locations
  some (name ++ "(" ++ joinStringsWith "," canonicals ++ ")")

/- BUG#6: LIBRARY-qualified signature rendering. solc renders public/external
   LIBRARY function signatures with the parameters' SOURCE types by canonical
   name (verified against solc 0.8.35 `--hashes`):
   * enum -> `Lib.Mode` (declaring-scope-qualified; file-level: `Mode`)
   * struct -> `Lib.S` (by NAME, not the external tuple form)
   * contract/interface -> `C` (its name, not `address`)
   * `storage`-pointer params keep the ` storage` suffix
   * user-defined value types erase to their UNDERLYING type (`uint128`),
     matching the external form — the existing UDVT erasure is already right.
   Everything else (uint/bytes/arrays/...) renders exactly as the external
   ABI form. Used ONLY at the library boundary: `L.f.selector` resolution,
   the library dispatch table, the delegatecall payload, and the type-env
   key. Contract dispatch/event/error selectors keep `Ty.abiCanonical?`. -/

def Path.canonicalString (path : Path) : String :=
  joinStringsWith "." path.segments

def StructDecl.canonicalPath (decl : StructDecl) : Path :=
  match decl.declScope? with
  | some scope => qualifiedPath scope decl.name
  | none => pathOfName decl.name

/-- Canonicalize a struct's WRITTEN path (`S` inside `Lib`, or `Lib.S`)
    through the same `StructEnv` that resolved it; falls back to the written
    path (already canonical for file-level structs). -/
def StructEnv.canonicalPath (env : StructEnv) (written : Path) : Path :=
  match StructEnv.lookup? env written with
  | some decl => StructDecl.canonicalPath decl
  | none => written

def Ty.libraryAbiCanonicalFuel? (structEnv : StructEnv) :
    Nat -> Ty -> Option String
  | 0, _ => none
  | _ + 1, Ty.enum canonical _ => some (Path.canonicalString canonical)
  | _ + 1, Ty.struct path _ =>
      some (Path.canonicalString (StructEnv.canonicalPath structEnv path))
  | _ + 1, Ty.user path => some (Path.canonicalString path)
  | fuel + 1, Ty.array ty none => do
      let base ← Ty.libraryAbiCanonicalFuel? structEnv fuel ty
      some (base ++ "[]")
  | fuel + 1, Ty.array ty (some size) => do
      let base ← Ty.libraryAbiCanonicalFuel? structEnv fuel ty
      some (base ++ "[" ++ toString size ++ "]")
  | _ + 1, other => Ty.abiCanonical? other

def Ty.libraryAbiCanonical? (structEnv : StructEnv) (ty : Ty) :
    Option String :=
  Ty.libraryAbiCanonicalFuel? structEnv 64 ty

def Ty.libraryAbiCanonicalWithLocation? (structEnv : StructEnv) (ty : Ty)
    (loc : Option DataLocation) : Option String := do
  let base ← Ty.libraryAbiCanonical? structEnv ty
  if dataLocationIsStorage loc then
    some (base ++ " storage")
  else
    some base

def Tys.listLibraryAbiCanonicalWithLocations? (structEnv : StructEnv) :
    List Ty -> List (Option DataLocation) -> Option (List String)
  | [], _ => some []
  | ty :: tys, locs => do
      let head ←
        Ty.libraryAbiCanonicalWithLocation? structEnv ty (locs.headD none)
      let tail ←
        Tys.listLibraryAbiCanonicalWithLocations? structEnv tys locs.tail
      some (head :: tail)

def libraryFunctionSignatureWithLocations? (structEnv : StructEnv)
    (name : Name) (argTys : List Ty)
    (locations : List (Option DataLocation)) : Option String := do
  let canonicals ←
    Tys.listLibraryAbiCanonicalWithLocations? structEnv argTys locations
  some (name ++ "(" ++ joinStringsWith "," canonicals ++ ")")

structure ExternalCallKindEntry where
  contractName : Name
  functionName : Name
  paramTys : List Ty := []
  paramNames : List (Option Name) := []
  -- Reference-signature extension: the source data location of each parameter.
  -- Only the external/public LIBRARY boundary carries `storage`-location
  -- parameters (`T storage self`), which solc passes by SLOT in the
  -- delegatecall calldata and renders `... storage` in the ABI signature. An
  -- empty list means "no location information" (treated as all-`none`).
  paramLocations : List (Option DataLocation) := []
  returnTys : List Ty := []
  mutability : StateMutability := StateMutability.nonpayable
  isConstructor : Bool := false
  -- BUG#6: for a public/external LIBRARY function, the library-qualified
  -- signature (`isOff(Lib.Mode)`, `bump(Lib.S storage)`) that the caller-side
  -- delegatecall payload must hash. `none` for contract entries — those keep
  -- the external-ABI signature.
  librarySignature? : Option String := none
  deriving Repr

abbrev ExternalCallKindEnv := List ExternalCallKindEntry

def constructorExternalCallKindName : Name :=
  "__solidcore_constructor"

def ExternalCallKindEnv.lookup? (env : ExternalCallKindEnv)
    (contractName functionName : Name) (paramTys : List Ty) :
    Option StateMutability :=
  match env with
  | [] => none
  | entry :: rest =>
      if !entry.isConstructor &&
          entry.contractName == contractName &&
          entry.functionName == functionName &&
          entry.paramTys == paramTys then
        some entry.mutability
      else
        ExternalCallKindEnv.lookup? rest contractName functionName paramTys

def ExternalCallKindEnv.lookupCallKind? (env : ExternalCallKindEnv)
    (contractName functionName : Name) (paramTys : List Ty) :
    Option CoreLowLevelCallKind :=
  match ExternalCallKindEnv.lookup? env contractName functionName paramTys with
  | some mutability => some (StateMutability.externalFunctionCallKind mutability)
  | none => none

def externalCallKindTypeEnvPrefix : Name :=
  "__external_call_kind:"

def externalCallKindTypeEnvName? (contractName functionName : Name)
    (paramTys : List Ty) : Option Name := do
  let signature ← externalFunctionSignature? functionName paramTys
  -- BUG#6: the external-ABI signature collapses user-defined types (every
  -- enum renders `uint8`), so two distinct LIBRARY overloads
  -- (`f(EnumA)`/`f(EnumB)` — solc-accepted, distinct qualified signatures)
  -- shared one key and one mutability/kind entry. Append a structural
  -- identity of the resolved parameter types (derived `repr`, which carries
  -- the canonical enum path and struct path) — computed identically at entry
  -- build and lookup, so the key stays symmetric. Repr-identity only: the
  -- key never reaches an ABI boundary.
  some
    (externalCallKindTypeEnvPrefix ++ contractName ++ ":" ++ signature ++
      "#" ++ toString (repr paramTys))

def ExternalCallKindEntry.toTypeEnvEntry?
    (entry : ExternalCallKindEntry) : Option (Option (Name × Ty)) := do
  if entry.isConstructor then
    some none
  else
    let key ←
      externalCallKindTypeEnvName?
        entry.contractName entry.functionName entry.paramTys
    some
      (some
        ( key
        , Ty.function entry.paramTys entry.returnTys entry.mutability
            Visibility.external_ ))

def ExternalCallKindEnv.toTypeEnv? (env : ExternalCallKindEnv) :
    Option TypeEnv :=
  filterMapOption ExternalCallKindEntry.toTypeEnvEntry? env

def TypeEnv.externalCallKindEntries (env : TypeEnv) : TypeEnv :=
  env.filter (fun entry => entry.fst.startsWith externalCallKindTypeEnvPrefix)

def TypeEnv.lookupExternalMutability? (env : TypeEnv)
    (contractName functionName : Name) (paramTys : List Ty) :
    Option StateMutability := do
  let key ← externalCallKindTypeEnvName? contractName functionName paramTys
  let ty ← TypeEnv.lookup? env key
  match ty with
  | Ty.functionWithLocations _ _ _ _ mutability Visibility.external_ =>
      some mutability
  | _ => none

def TypeEnv.lookupExternalCallKind? (env : TypeEnv)
    (contractName functionName : Name) (paramTys : List Ty) :
    Option CoreLowLevelCallKind := do
  let mutability ←
    TypeEnv.lookupExternalMutability? env contractName functionName paramTys
  some (StateMutability.externalFunctionCallKind mutability)

/-- Special-case lowering for the operand of a `bytes(...)`/`string(...)`
    dynamic conversion. Handles exactly the operand shapes that must NOT be
    lowered by the generic recursion because they need a dedicated core node
    or an identity read:
    * a bare identifier -- a storage `bytes`/`string` lowers to `storageBytes`
      (its length-prefixed layout), any other identifier to its plain core;
    * a `bytes`/`string` literal;
    * a `bytes(ident)`/`string(ident)` re-wrap (same storage/memory split).
    Returns `none` for a general operand (index / member / call / nested
    conversion / ternary), which the caller lowers by the ordinary recursion
    (string<->bytes being a pointer reinterpret, i.e. identity, in the core
    model). This mirrors the previous inline `match expr` cases so their
    behavior is preserved exactly; factoring them out lets the caller keep the
    recursive call off a `match expr` wildcard (needed for termination). -/
def Expr.bytesStringSpecialCore? (storageNames : List Name) :
    Expr -> Option CoreExpr
  | Expr.ident name =>
      match stateNameRuntimeKey? name storageNames with
      | some key => some (SolidCore.Solidity.Source.Expr.storageBytes key)
      | none => some (sourceIdentCore storageNames name)
  | Expr.literal literal =>
      match Literal.abiTy? literal with
      | some Ty.bytes | some Ty.string => Literal.toCoreExpr? literal
      | _ => none
  | Expr.call (Expr.typeName Ty.bytes) [Arg.positional (Expr.ident name)]
  | Expr.call (Expr.typeName Ty.string) [Arg.positional (Expr.ident name)] =>
      match stateNameRuntimeKey? name storageNames with
      | some key => some (SolidCore.Solidity.Source.Expr.storageBytes key)
      | none => some (sourceIdentCore storageNames name)
  | _ => none

/-- PUSH-FIELD-LVALUE: peel any trailing index accessors off an lvalue whose
    innermost base is a zero-arg storage-array `.push()` call. Returns the
    array target expression and the trailing index expressions in
    application order (outermost-last), or `none` when the base is not such a
    push. `xs.push().a` reaches here already rewritten to
    `xs.push()[fieldIndex]` by `resolveStructsFuel`; `ys.push()[i]` arrives
    directly. Structural recursion on the index spine. -/
def Expr.stripPushIndexPath? : Expr -> Option (Expr × List Expr)
  | Expr.call (Expr.member target "push") [] => some (target, [])
  | Expr.index base index => do
      let (target, idxs) ← Expr.stripPushIndexPath? base
      some (target, idxs ++ [index])
  | _ => none

/- R3 (#192) endgame: the per-boundary `materializeStorageValueUseCore`
   rewrite is GONE. Storage value-use materialization is now performed by the
   single total position-aware pass
   `SolidCore.Solidity.Source.Stmt.normalizeStorageValueUses` (see
   Interpreter.lean), applied once to every emitted core function body
   (`FunctionDecl.toCore?` / `ContractDecl.constructorFunctionFromOrders?`).
   The mode flip itself lives on the unified `Expr.storageRead` constructor
   (`header` -> `load`). -/

set_option maxHeartbeats 1000000 in
mutual

/-- WS1 Stage 3 (dedup): the depth-2 `address(T(inner))` conversion lowering,
    shared verbatim by the plain arm and the `payable(address(T(inner)))`
    (`Expr.payableConversion`) arm of `Expr.toCore?` — previously two
    byte-identical 80-line copies. Behavior unchanged. -/
def Expr.addressOfNestedConversionCore? (storageNames : List Name)
    (innerTy : Ty) (innerExpr : Expr) : Option CoreExpr :=
      match innerTy with
      | Ty.address _ =>
          match Expr.toCoreAddressLiteral? innerExpr with
          | some coreExpr => some coreExpr
          | none =>
              -- Bail with `none` ONLY for a genuine bare-literal candidate that
              -- failed to fold (an out-of-range address literal — solc rejects
              -- those). When `innerExpr` is itself a nested conversion such as
              -- `address(0x1234)` (an identity `address(...)` chain at depth
              -- >= 3), `isAddressLiteralCandidate` also returns `true` (it
              -- recurses into the inner literal), but bailing there would fail to
              -- lower an otherwise-accepted chain. So recurse in that case and let
              -- the single-conversion arm fold the inner cast; a genuinely
              -- out-of-range inner literal stays rejected (the inner fold = none).
              if Expr.isAddressLiteralCandidate innerExpr &&
                  !Expr.isConversionCall innerExpr then
                none
              else
                Expr.toCore? storageNames innerExpr
      | Ty.uint 160 =>
          match Expr.toCoreNumericLiteralAs? innerTy innerExpr with
          | some coreExpr => some coreExpr
          | none =>
              -- Only a RAW rational literal must fit uint160 exactly.  A
              -- typed inner conversion such as uint160(uint256(max)) is a
              -- run-time truncation that solc accepts; isNumberLiteralExpression
              -- deliberately looks through that conversion and used to reject
              -- the accepted address(uint160(uint256(max))) composition.
              if Expr.isRawNumberLiteralExpression innerExpr then
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
termination_by (sizeOf innerExpr, 1)


def Expr.toCore? (storageNames : List Name) : Expr -> Option CoreExpr
  | Expr.literal literal => Literal.toCoreExpr? literal
  | Expr.ident name =>
      some (sourceIdentCore storageNames name)
  | Expr.member (Expr.typeName ty) member =>
      match Ty.typeInfoExpr? ty member with
      | some info => some info
      | none =>
          -- Qualified (inherited) STATE-VARIABLE read through a type name
          -- (`Base.v`): resolves to the same storage/immutable slot as the bare
          -- identifier. Constants were already inlined; only storage-backed
          -- names reach here.
          match ty with
          | Ty.user _ =>
              match stateNameRuntimeKey? member storageNames with
              | some key =>
                  some (SolidCore.Solidity.Source.Expr.storageIdent key)
              | none =>
                  match stateNameImmutableKey? member storageNames with
                  | some key =>
                      some (SolidCore.Solidity.Source.Expr.immutable key)
                  | none => none
          | _ => none
  | Expr.call (Expr.typeName (Ty.address _))
      [Arg.positional (Expr.call (Expr.typeName innerTy)
        [Arg.positional innerExpr])] =>
      Expr.addressOfNestedConversionCore? storageNames innerTy innerExpr
  | Expr.call (Expr.typeName Ty.string)
      [Arg.positional
        (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") args)] => do
      let (sourceTys, coreTys, exprs) ← Args.toAbiEncodeSource? storageNames args
      some (SolidCore.Solidity.Source.Expr.abiEncodePacked
        (Tys.packedTopWidths sourceTys) coreTys
        exprs)
  | Expr.call (Expr.typeName targetTy)
      [Arg.positional
        (Expr.member (Expr.typeName sourceTy@(Ty.user _)) "name")] =>
      if targetTy == Ty.bytes || targetTy == Ty.string then
        Ty.typeInfoExpr? sourceTy "name"
      else
        none
  | Expr.call (Expr.typeName Ty.bytes)
      [Arg.positional (Expr.index (Expr.ident name) index)] =>
      match stateNameRuntimeKey? name storageNames with
      | some key =>
        do
        let indexCore ← Expr.toCore? storageNames index
        some (SolidCore.Solidity.Source.Expr.storageIndex key indexCore)
      | none =>
        do
        let baseCore ← Expr.toCore? storageNames (Expr.ident name)
        let indexCore ← Expr.toCore? storageNames index
        some (SolidCore.Solidity.Source.Expr.index baseCore indexCore)
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
      -- FNPTR-STRUCT-CONSTRUCTOR (value production): a struct constructor
      -- `S(f, …)` is lowered (`resolveStructs`) to a tuple whose fn-pointer
      -- FIELD becomes `function(...)(<dispatch-id>)` — a conversion of the
      -- rewritten dispatch-ID number literal to the field's internal-function
      -- type. This TARGET-LESS `toCore?` path (used by the struct/tuple element
      -- lowering) must reproduce the SAME value the target-aware `toCoreAs?`
      -- (§5519) and env-aware `toCoreAsWithEnv?` (§8602) do — an
      -- `Expr.internalFunction` pointer value, NOT the raw word the numeric
      -- fall-through below would yield. Without this the field holds a bare word
      -- and a later call through it hits the pointer-call type-mismatch (Panic 0)
      -- instead of dispatching.
      match Expr.toCoreInternalFunctionValueLiteralAs? ty expr with
      | some coreExpr => some coreExpr
      | none =>
      match Expr.toCoreFixedBytesLiteralAs? ty expr with
      | some coreExpr => some coreExpr
      | none =>
          if Ty.isFixedBytes ty &&
              Expr.isFixedBytesLiteralCandidate expr then
            none
          else
            match Ty.fixedBytesSize? ty with
            | some targetSize => do
                match Expr.abiTy? storageNames expr with
                | some sourceTy =>
                    match sourceTy with
                    | Ty.bytes => do
                        let coreExpr ← Expr.toCore? storageNames expr
                        some
                          (SolidCore.Solidity.Source.Expr.fixedBytesFromBytes
                            targetSize coreExpr)
                    | _ => do
                        let sourceSize ←
                          Ty.fixedBytesCastWordSourceSize?
                            targetSize sourceTy
                        let coreExpr ← Expr.toCore? storageNames expr
                        some
                          (SolidCore.Solidity.Source.Expr.fixedBytesCast
                            targetSize sourceSize coreExpr)
                | none => do
                    let _ ← Ty.toCore? ty
                    let coreExpr ← Expr.toCore? storageNames expr
                    -- FB1: a `bytesN` cast whose OPERAND has no env-less
                    -- `Expr.abiTy?` (a `<<` over a local/param/storage `bytesN`,
                    -- whose leaf identifier carries no `abiTy?` arm) still needs
                    -- the lane cleanup solc emits after every `bytesN <<`
                    -- (`cleanup_t_bytesN`). solidity-lean stores `bytesN`
                    -- right-aligned, so a LEFT shift pushes meaningful bits above
                    -- the low `size`-byte lane; DROPPING the cast (lowering the
                    -- operand bare, as this branch did) leaves those stray bits,
                    -- so the consumer — here the ABI encoder that `annotateAbi`
                    -- wraps as `bytesN(b << 8)` — sees a mis-shaped value and
                    -- Panics 0. Re-mask with `implicitCleanupCore` at the target
                    -- `bytesN`, exactly as the bound-local path (`bytes4 r =
                    -- b << 8`) already does. It is the identity for any
                    -- non-left-shift operand, so every other unknown-source
                    -- `bytesN` cast keeps its prior bare lowering byte-identically.
                    some (Ty.implicitCleanupCore (Ty.bytesN targetSize) coreExpr)
            | none =>
                match Expr.toCoreNumericLiteralAs? ty expr with
                | some coreExpr => some coreExpr
                | none =>
                  if Ty.isIntOrUint ty &&
                        Expr.isRawNumberLiteralExpression expr then
                      none
                    else
                      match ty with
                      | Ty.bytes | Ty.string =>
                          -- `bytes(...)`/`string(...)` of a dynamic operand.
                          -- The special-case operands (a bare identifier,
                          -- a `bytes`/`string` literal, or a
                          -- `bytes(ident)`/`string(ident)` re-wrap -- including
                          -- storage bytes/string that must lower to
                          -- `storageBytes`) are handled by
                          -- `Expr.bytesStringSpecialCore?`, preserving prior
                          -- behavior exactly. Any OTHER operand (index / member
                          -- / call / nested conversion / ternary / etc.) is a
                          -- pointer REINTERPRET (string<->bytes is identity in
                          -- the core model), so we lower it by the normal
                          -- recursion and return its core expr directly. The
                          -- underlying node decides copy vs alias: a memory read
                          -- (`Expr.index`) aliases, a storage read
                          -- (`storageIndex`/`storageBytes`) deep-copies into
                          -- memory, and a calldata descriptor is reinterpreted
                          -- -- matching solc. The recursion sits directly under
                          -- the `Expr.bytesStringSpecialCore?` match (not a
                          -- `match expr`) so the well-founded subterm fact stays
                          -- available. We recurse unconditionally: this is
                          -- already the `bytes`/`string` conversion TARGET, so
                          -- the operand is a dynamic bytes/string (guaranteed by
                          -- the typechecker) and the reinterpret is identity.
                          -- `annotateAbi` renders the operand as
                          -- `<sourceTy>(inner)` (e.g. `bytes(string(s[0]))`),
                          -- whose element type the env-free `Expr.abiTy?` cannot
                          -- always recover, so it must not gate the recursion.
                          -- If the operand cannot be lowered the recursion still
                          -- yields `none`, exactly as before.
                          match Expr.bytesStringSpecialCore? storageNames expr with
                          | some core => some core
                          | none => Expr.toCore? storageNames expr
                      | _ =>
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
  | Expr.member base "selector" => do
      let baseCore ← Expr.toCore? storageNames base
      some
        (SolidCore.Solidity.Source.Expr.externalFunctionSelector baseCore)
  | Expr.member base "address" => do
      let baseCore ← Expr.toCore? storageNames base
      some
        (SolidCore.Solidity.Source.Expr.externalFunctionAddress baseCore)
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
  | Expr.newExpr Ty.string [Arg.positional lengthExpr] => do
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
          none true)
  | Expr.callWithOptions (Expr.newExpr ty []) options args => do
      let contractName ← Ty.contractName? ty
      let (valueCore?, saltCore?, valueBeforeSalt) ←
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
          valueCore saltCore? valueBeforeSalt)
  | Expr.call (Expr.member target "call") [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.toCore? storageNames payload
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.call
          targetCore payloadCore (SolidCore.Solidity.Source.Expr.word 0)
          none false)
  | Expr.callWithOptions (Expr.member target "call")
      options [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.toCore? storageNames payload
      let (valueCore, gasCore?, gasFirst) ←
        CallOptions.lowLevelCallValueGasCore? storageNames options
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.call
          targetCore payloadCore valueCore gasCore? gasFirst)
  | Expr.call (Expr.member target "staticcall") [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.toCore? storageNames payload
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.staticcall
          targetCore payloadCore (SolidCore.Solidity.Source.Expr.word 0)
          none false)
  | Expr.callWithOptions (Expr.member target "staticcall")
      options [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.toCore? storageNames payload
      let (valueCore, gasCore?, gasFirst) ←
        CallOptions.lowLevelDelegateGasCore? storageNames options
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.staticcall
          targetCore payloadCore valueCore gasCore? gasFirst)
  | Expr.call (Expr.member target "delegatecall") [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.toCore? storageNames payload
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.delegatecall
          targetCore payloadCore (SolidCore.Solidity.Source.Expr.word 0)
          none false)
  | Expr.callWithOptions (Expr.member target "delegatecall")
      options [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.toCore? storageNames payload
      let (valueCore, gasCore?, gasFirst) ←
        CallOptions.lowLevelDelegateGasCore? storageNames options
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.delegatecall
          targetCore payloadCore valueCore gasCore? gasFirst)
  | Expr.call (Expr.member target "send") [Arg.positional value] => do
      let targetCore ← Expr.toCore? storageNames target
      let valueCore ← Expr.toCore? storageNames value
      some
        (SolidCore.Solidity.Source.Expr.index
          (SolidCore.Solidity.Source.Expr.lowLevelCall
            SolidCore.Solidity.Source.LowLevelCallKind.call
            targetCore
            (SolidCore.Solidity.Source.Expr.byteArray [])
            valueCore
            (some (SolidCore.Solidity.Source.Expr.word 2300))
            false)
          (SolidCore.Solidity.Source.Expr.word 0))
  | Expr.call (Expr.member (Expr.ident "abi") "encode") args => do
      let (tys, exprs) ← Args.toAbiEncode? storageNames args
      some
        (SolidCore.Solidity.Source.Expr.abiEncode tys
          exprs)
  | Expr.call (Expr.member (Expr.ident "abi") "decode")
      [Arg.positional data, Arg.positional typesExpr] => do
      let (tys, cleanups, dataCore) ←
        Expr.toAbiDecode? storageNames data typesExpr
      some
        (SolidCore.Solidity.Source.Expr.abiDecode tys cleanups dataCore)
  | Expr.call (Expr.member (Expr.ident "abi") "encodePacked") args => do
      let (sourceTys, coreTys, exprs) ← Args.toAbiEncodeSource? storageNames args
      some (SolidCore.Solidity.Source.Expr.abiEncodePacked
        (Tys.packedTopWidths sourceTys) coreTys
        exprs)
  | Expr.call (Expr.member (Expr.ident "abi") "encodeWithSelector")
      (Arg.positional selector :: args) => do
      -- LIT-COERCION (#143): the leading selector argument is `bytes4`. A `bytes4`
      -- (or `bytesN 4`) VALUE/expression lowers directly. A bare hex NUMBER literal
      -- whose byte-width is exactly 4 (e.g. `0x12345678`) has `abiTy? = uint256`
      -- but solc implicitly converts it to `bytes4` (its exact-width compatible
      -- bytes type), so fall back to the target-aware literal coercion. That
      -- coercion is width-exact: a 2-byte hex literal (`0x1234`, compatible type
      -- `bytes2`, NOT implicitly `bytes4`) and any decimal literal both yield
      -- `none` here — matching solc, which rejects them.
      let selectorCore ←
        match Expr.abiTy? storageNames selector with
        | some (Ty.bytesN 4) => Expr.toCore? storageNames selector
        | some (Ty.fixedBytes 4) => Expr.toCore? storageNames selector
        | _ => Expr.toCoreFixedBytesLiteralAs? (Ty.fixedBytes 4) selector
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
      let (sourceTys, coreTys, coreExprs) ←
        TupleItems.toAbiEncodeSource? storageNames items
      let selectorCore ←
        Expr.functionPointerSelectorCore?
          storageNames functionPointer sourceTys
      some
        (SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
          selectorCore
          coreTys coreExprs)
  | Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
      [Arg.positional functionPointer, Arg.positional argumentExpr] => do
      let (sourceTy, coreTy, coreExpr) ←
        Expr.toAbiEncodeSourceArg? storageNames argumentExpr
      let selectorCore ←
        Expr.functionPointerSelectorCore?
          storageNames functionPointer [sourceTy]
      some
        (SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
          selectorCore [coreTy]
          [coreExpr])
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
      some
        (SolidCore.Solidity.Source.Expr.keccak256
          bytesCore)
  | Expr.call (Expr.ident "erc7201") [Arg.positional id] => do
      let idCore ← Expr.toCore? storageNames id
      some
        (SolidCore.Solidity.Source.Expr.erc7201
          idCore)
  | Expr.call (Expr.ident "sha256") [Arg.positional bytes] => do
      let bytesCore ← Expr.toCore? storageNames bytes
      some
        (SolidCore.Solidity.Source.Expr.externalHash
          SolidCore.Solidity.Source.ExternalHashKind.sha256
          bytesCore)
  | Expr.call (Expr.ident "ripemd160") [Arg.positional bytes] => do
      let bytesCore ← Expr.toCore? storageNames bytes
      some
        (SolidCore.Solidity.Source.Expr.externalHash
          SolidCore.Solidity.Source.ExternalHashKind.ripemd160
          bytesCore)
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
          (Tys.packedTopWidths sourceTys) coreTys
          coreExprs)
      else
        none
  | Expr.call (Expr.member (Expr.typeName Ty.bytes) "concat") args => do
      let (sourceTys, coreTys, coreExprs) ←
        Args.toAbiEncodeSource? storageNames args
      if Tys.allBytesConcatArgs sourceTys then
        some (SolidCore.Solidity.Source.Expr.abiEncodePacked
          (Tys.packedTopWidths sourceTys) coreTys
          coreExprs)
      else
        none
  | Expr.call (Expr.member (Expr.ident "string") "concat") args => do
      let (sourceTys, coreTys, coreExprs) ←
        Args.toAbiEncodeSource? storageNames args
      -- `string.concat` and `bytes.concat` lower identically (packed byte
      -- concatenation); the typechecker (`checkStringConcatArgs`) is the
      -- acceptance authority, admitting `string`/`unicode` literals and
      -- valid-UTF-8 `hex"…"` literals (the latter typed `Ty.bytes`). So gate the
      -- lowering on the broader `allBytesConcatArgs`, which admits both `Ty.string`
      -- and the `Ty.bytes` hex-literal form; anything else was already rejected.
      if Tys.allBytesConcatArgs sourceTys then
        some (SolidCore.Solidity.Source.Expr.abiEncodePacked
          (Tys.packedTopWidths sourceTys) coreTys
          coreExprs)
      else
        none
  | Expr.call (Expr.member (Expr.typeName Ty.string) "concat") args => do
      let (sourceTys, coreTys, coreExprs) ←
        Args.toAbiEncodeSource? storageNames args
      if Tys.allBytesConcatArgs sourceTys then
        some (SolidCore.Solidity.Source.Expr.abiEncodePacked
          (Tys.packedTopWidths sourceTys) coreTys
          coreExprs)
      else
        none
  | Expr.member (Expr.ident name) "length" =>
      match stateNameRuntimeKey? name storageNames with
      | some key =>
        some (SolidCore.Solidity.Source.Expr.storage key)
      | none =>
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
      match stateNameRuntimeKey? name storageNames with
      | some key =>
        do
        let indexCore ← Expr.toCore? storageNames index
        -- R3 (#192): a mapping/array INDEX KEY is a VALUE-USE boundary — the key
        -- CONTENTS feed the value-slot hash (`mappingStorageSlotForKey`). A bare
        -- state `string`/`bytes`/array key lowers to `Expr.storage key`, whose
        -- eval is the HEADER word (the `.length` convention), so an unmaterialized
        -- key fed the header word to the hash → `typeMismatch` = Panic(0). solc
        -- copies the storage string/bytes to memory before deriving the slot, so
        -- `m[stateStr]` and `m["lit"]` hit the SAME slot. Materialize the key core
        -- so its full contents are read; scalar keys load identically either way.
        some (SolidCore.Solidity.Source.Expr.storageIndex key
          indexCore)
      | none =>
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
  | Expr.unary UnaryOp.neg (Expr.literal (Literal.number text)) => do
      -- A bare negated numeric literal `-5` is an `int_const` in solc, not a
      -- checked negation of an unsigned word. The env-less fallback formerly
      -- lowered it to `-(word 5)`, which Panics 0x11 under a checked unary `-`
      -- on an unsigned operand (e.g. `signedArray.push(-5)`; the type-directed
      -- paths, H1, cover the arithmetic sites). Fold to a signed constant.
      let n ← parseNumberNat? text
      some
        (SolidCore.Solidity.Source.Expr.intWord
          (SolidCore.Solidity.Shared.signedToWord (-(Int.ofNat n))))
  | Expr.unary UnaryOp.neg (Expr.literal (Literal.unitNumber text unit)) => do
      let n ← parseUnitNumberNat? text unit
      some
        (SolidCore.Solidity.Source.Expr.intWord
          (SolidCore.Solidity.Shared.signedToWord (-(Int.ofNat n))))
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
      let lowerBinary : Option CoreExpr := do
        let coreOp ← BinaryOp.toCore? op
        let lhsCore ← Expr.toCore? storageNames lhs
        let rhsCore ← Expr.toCore? storageNames rhs
        some (SolidCore.Solidity.Source.Expr.binary coreOp lhsCore rhsCore)
      -- An explicitly typed left operand fixes a shift's result width. Do not
      -- erase that boundary with the rational constant folder: for example,
      -- `uint8(91) << uint8(8)` is zero after truncation, not the out-of-range
      -- rational 23296 followed by a checked-cleanup Panic(0x11).
      match op, lhs with
      | BinaryOp.shl, Expr.call (Expr.typeName lhsTy) [Arg.positional _] =>
          if Ty.isIntOrUint lhsTy then do
            let core ← lowerBinary
            Ty.implicitCleanupCore? lhsTy core
          else
            lowerBinary
      | _, _ =>
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
              | none => lowerBinary
  | Expr.ternary cond thenExpr elseExpr => do
      let condCore ← Expr.toCore? storageNames cond
      let thenCore ← Expr.toCore? storageNames thenExpr
      let elseCore ← Expr.toCore? storageNames elseExpr
      some (SolidCore.Solidity.Source.Expr.ternary
        condCore thenCore elseCore)
  | Expr.tuple items => do
      let coreExprs ← TupleItems.toCoreExprs? storageNames items
      -- TUPLE-RHS VALUE-USE: a value-position tuple `(a, …, z)` (the RHS of a
      -- tuple assignment / declaration, e.g. `(bytes memory b, uint x) = (src,
      -- 5)`) reads each component BY VALUE. A bare state `bytes`/`string`/array
      -- component lowers to `Expr.storage key` (the storage HEADER word, the
      -- `.length` convention); copying that word into a memory local feeds a
      -- non-materialized header to the value boundary → `asBytes?` = `none` →
      -- `Panic(0)`. Materialize each component (`Expr.storage key` →
      -- `Expr.storagePath key []`) so the contents are copied, matching the
      -- other value-use boundaries; every scalar/reference core passes through.
      some (SolidCore.Solidity.Source.Expr.tuple
        coreExprs)
  | Expr.array exprs => do
      let targetTy ← Expr.arrayLiteralCommonTy? storageNames exprs
      let coreExprs ←
        Expr.arrayLiteralCoreExprsAs? storageNames targetTy exprs
      some (SolidCore.Solidity.Source.Expr.fixedArray coreExprs)
  | Expr.payableConversion
      (Expr.call (Expr.typeName (Ty.address _))
        [Arg.positional (Expr.call (Expr.typeName innerTy)
          [Arg.positional innerExpr])]) =>
      Expr.addressOfNestedConversionCore? storageNames innerTy innerExpr
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

def CallOptions.lowLevelCallValueGasCore? (storageNames : List Name) :
    List CallOption -> Option (CoreExpr × Option CoreExpr × Bool)
  | [] => some (CoreExpr.zero, none, false)
  | [CallOption.named "gas" gas] => do
      let gasCore ← Expr.toCore? storageNames gas
      some (CoreExpr.zero, some gasCore, true)
  | [CallOption.named "value" value] => do
      let valueCore ← Expr.toCore? storageNames value
      some (valueCore, none, false)
  | [CallOption.named "gas" gas, CallOption.named "value" value] => do
      let gasCore ← Expr.toCore? storageNames gas
      let valueCore ← Expr.toCore? storageNames value
      some (valueCore, some gasCore, true)
  | [CallOption.named "value" value, CallOption.named "gas" gas] => do
      let valueCore ← Expr.toCore? storageNames value
      let gasCore ← Expr.toCore? storageNames gas
      some (valueCore, some gasCore, false)
  | _ => none
termination_by options => (sizeOf options, 0)

def CallOptions.lowLevelDelegateGasCore? (storageNames : List Name) :
    List CallOption -> Option (CoreExpr × Option CoreExpr × Bool)
  | [] => some (CoreExpr.zero, none, false)
  | [CallOption.named "gas" gas] => do
      let gasCore ← Expr.toCore? storageNames gas
      some (CoreExpr.zero, some gasCore, true)
  | _ => none
termination_by options => (sizeOf options, 0)

-- Returns `(value?, salt?, valueBeforeSalt)`; `valueBeforeSalt` preserves the
-- source order of the two options (solc evaluates them in source order —
-- DIV-CREATE-2).  It is only observed when both options are present.
def CallOptions.contractCreationValueSaltCore? (storageNames : List Name) :
    List CallOption -> Option (Option CoreExpr × Option CoreExpr × Bool)
  | [] => some (none, none, true)
  | [CallOption.named "value" value] => do
      let valueCore ← Expr.toCore? storageNames value
      some (some valueCore, none, true)
  | [CallOption.named "salt" salt] => do
      let saltCore ← Expr.toCore? storageNames salt
      some (none, some saltCore, true)
  | [CallOption.named "value" value, CallOption.named "salt" salt] => do
      let valueCore ← Expr.toCore? storageNames value
      let saltCore ← Expr.toCore? storageNames salt
      some (some valueCore, some saltCore, true)
  | [CallOption.named "salt" salt, CallOption.named "value" value] => do
      let saltCore ← Expr.toCore? storageNames salt
      let valueCore ← Expr.toCore? storageNames value
      some (some valueCore, some saltCore, false)
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

def Expr.isDirectLiteral : Expr -> Bool
  | Expr.literal _ => true
  | _ => false

def implicitLiteralFits (target : Ty) (expr : Expr) : Bool :=
  match Expr.toCoreNumericLiteralAs? target expr with
  | some _ => true
  | none =>
      match Expr.toCoreFixedBytesLiteralAs? target expr with
      | some _ => true
      | none => false

def arrayLiteralCommonInfo?
    (left right : Expr × Ty) : Option (Expr × Ty) :=
  if Expr.isDirectLiteral right.fst &&
      implicitLiteralFits left.snd right.fst then
    some (left.fst, left.snd)
  else if Expr.isDirectLiteral left.fst &&
      implicitLiteralFits right.snd left.fst then
    some (right.fst, right.snd)
  else do
    let ty ← Ty.commonImplicit? left.snd right.snd
    some (right.fst, ty)

def Expr.arrayLiteralCommonInfoFrom? (storageNames : List Name)
    (current : Expr × Ty) :
    List Expr -> Option (Expr × Ty)
  | [] => some current
  | expr :: rest => do
      let ty ← Expr.abiTy? storageNames expr
      let next ← arrayLiteralCommonInfo? current (expr, ty)
      Expr.arrayLiteralCommonInfoFrom? storageNames next rest
termination_by exprs => (sizeOf exprs, 1)

def Expr.arrayLiteralCommonTy? (storageNames : List Name) :
    List Expr -> Option Ty
  | [] => none
  | first :: rest => do
      let firstTy ← Expr.abiTy? storageNames first
      let info ←
        Expr.arrayLiteralCommonInfoFrom? storageNames (first, firstTy) rest
      some info.snd
termination_by exprs => (sizeOf exprs, 2)

def Expr.toCoreStorageByteStringAs? (storageNames : List Name)
    (targetTy : Ty) : Expr -> Option CoreExpr
  | Expr.ident name =>
      match targetTy with
      | Ty.bytes | Ty.string =>
          match stateNameRuntimeKey? name storageNames with
          | some key =>
              some (SolidCore.Solidity.Source.Expr.storageBytes key)
          | none => none
      | _ => none
  | _ => none

def Expr.toCoreStorageArrayAs? (storageNames : List Name)
    (targetTy : Ty) : Expr -> Option CoreExpr
  | Expr.ident name =>
      match targetTy with
      | Ty.array _ _ =>
          match stateNameRuntimeKey? name storageNames with
          | some key =>
              some (SolidCore.Solidity.Source.Expr.storagePath key [])
          | none => none
      | _ => none
  | _ => none

def Expr.nestedStoragePathCore? (storageNames : List Name) :
    Expr -> Option (Name × List CoreExpr)
  | Expr.ident name => do
      let key ← stateNameRuntimeKey? name storageNames
      some (key, [])
  | Expr.index base index => do
      let (name, indexes) ← Expr.nestedStoragePathCore? storageNames base
      let indexCore ← Expr.toCore? storageNames index
      some (name, indexes ++ [indexCore])
  | _ => none
termination_by expr => (sizeOf expr, 0)

/-- A fn-value number literal (the shape a bare function NAME takes after
    `rewriteInternalFnValueIdents`) targeted at an INTERNAL function type becomes
    the core internal-function-pointer value. This is the value-production site
    shared by every typed lowering context (var-decl init, comparison operand,
    return, argument), so a ternary/storage/comparison-derived internal function
    pointer carries `Value.internalFunction` everywhere — the same
    representation the env-aware `toCoreAsWithEnv?` produces for the direct
    initializer (kept in sync with `Interface.lean` §7133). A REAL number literal
    in an internal-fn position is rejected by the typechecker, so post-typecheck
    this shape is unambiguous; external function types are excluded. -/
def Expr.toCoreInternalFunctionValueLiteralAs? (targetTy : Ty) :
    Expr -> Option CoreExpr
  | Expr.literal (Literal.number text) =>
      if Ty.isInternalFunctionValueTy targetTy then
        (parseNumberNat? text).map
          SolidCore.Solidity.Source.Expr.internalFunction
      else
        none
  | _ => none

/-- AL-EXEC (executable lowering of an inline array literal into an array
    target). solc types an inline array literal bottom-up (smallest
    common mobile element type — `[1,2,3] : uint8[3]`) and a fixed→fixed
    memory-array conversion requires the target's element type to EQUAL that
    bottom-up element type (`ArrayType::isImplicitlyConvertibleTo`, non-copy
    branch; the AL1 typechecker enforces exactly this before we lower). The
    env-less `abiTy?` of a bare number literal is `uint256`, so the generic
    `toCoreAs?` array path (which requires the inferred source array type to
    equal the target) fails whenever the elements are undecorated narrow-int
    literals (`uint8[3] x = [1,2,3]`, `uint8[2][2] x = [[1,2],[3,4]]`), even
    though solc accepts and runs them. Here the target element type is the
    AL1-verified element type, so each element is lowered directly at `elemTy`
    (left-to-right, `arrayLiteralCoreExprsAs?` → `toCoreAs?`), and the whole
    literal becomes a fresh fixed memory array. Nested/multidim literals recurse
    because each element's `toCoreAs? elemTy` re-enters this arm. -/
def Expr.fixedArrayLiteralAs? (storageNames : List Name)
    (targetTy : Ty) (expr : Expr) : Option CoreExpr :=
  match targetTy, expr with
  | Ty.array elemTy (some n), Expr.array elems =>
      if elems.length == n then
        (Expr.arrayLiteralCoreExprsAs? storageNames elemTy elems).map
          SolidCore.Solidity.Source.Expr.fixedArray
      else
        none
  | Ty.array elemTy none, Expr.array elems =>
      -- Inline literals are fixed-size values even when a storage-copy target
      -- is dynamic (`int16[] x = [-1, -2]`). The typechecker has already
      -- established that the fixed source can be copied into the dynamic
      -- storage destination, so lower each element at the destination base
      -- type and retain the literal's fixed runtime value shape.
      (Expr.arrayLiteralCoreExprsAs? storageNames elemTy elems).map
        SolidCore.Solidity.Source.Expr.fixedArray
  | _, _ => none
termination_by (sizeOf expr, 0)

def Expr.toCoreAs? (storageNames : List Name)
    (targetTy : Ty) (expr : Expr) : Option CoreExpr :=
  match Expr.fixedArrayLiteralAs? storageNames targetTy expr with
  | some coreExpr => some coreExpr
  | none =>
  -- Materialize an array or byte-string member reached through a nested
  -- storage path in one operation. Recursively lowering `boxes[0].data` would
  -- load `boxes[0]` as a whole struct before selecting `data`; that is
  -- impossible when the struct also contains a mapping. Keeping the complete
  -- path resolves directly to the selected dynamic field.
  match
      (match targetTy, Expr.nestedStoragePathCore? storageNames expr with
      | Ty.array _ _, some (name, indexes) =>
          if indexes.isEmpty then none
          else some (SolidCore.Solidity.Source.Expr.storagePath name indexes)
      | Ty.bytes, some (name, indexes)
      | Ty.string, some (name, indexes) =>
          if indexes.isEmpty then none
          else some (SolidCore.Solidity.Source.Expr.storagePath name indexes)
      | _, _ => none)
  with
  | some coreExpr => some coreExpr
  | none =>
  match Expr.toCoreStorageArrayAs? storageNames targetTy expr with
  | some coreExpr => some coreExpr
  | none =>
      match Expr.toCoreStorageByteStringAs? storageNames targetTy expr with
      | some coreExpr => some coreExpr
      | none =>
          match Expr.toCoreFixedBytesLiteralAs? targetTy expr with
          | some coreExpr => some coreExpr
          | none =>
              if Ty.isFixedBytes targetTy &&
                  Expr.isFixedBytesLiteralCandidate expr then
                none
              else
                match Expr.toCoreInternalFunctionValueLiteralAs? targetTy expr with
                | some coreExpr => some coreExpr
                | none =>
                match Expr.toCoreNumericLiteralAs? targetTy expr with
                | some coreExpr => some coreExpr
                | none =>
                    if Ty.isIntOrUint targetTy &&
                        Expr.isRawNumberLiteralExpression expr then
                      none
                    else do
                      let sourceTy ← Expr.abiTy? storageNames expr
                      let coreExpr ← Expr.toCore? storageNames expr
                      if
                          (targetTy == Ty.bytes || targetTy == Ty.string) &&
                            (sourceTy == Ty.bytes || sourceTy == Ty.string) then
                        some coreExpr
                      else if sourceTy == targetTy then
                        Ty.implicitCleanupCore? targetTy coreExpr
                      else
                        match targetTy with
                    | Ty.uint bits => do
                        let bits := if bits == 0 then 256 else bits
                        let _ ← Ty.allowsUintCastSource? bits sourceTy
                        some
                          (SolidCore.Solidity.Source.Expr.uintCleanup
                            bits coreExpr)
                    | Ty.int bits => do
                        let bits := if bits == 0 then 256 else bits
                        let _ ← Ty.allowsIntCastSource? bits sourceTy
                        some
                          (SolidCore.Solidity.Source.Expr.intCleanup
                            bits coreExpr)
                    | Ty.bytesN targetSize
                    | Ty.fixedBytes targetSize =>
                        match sourceTy with
                        | Ty.bytes =>
                            some
                              (SolidCore.Solidity.Source.Expr.fixedBytesFromBytes
                                targetSize coreExpr)
                        | _ => do
                            let sourceSize ←
                              Ty.fixedBytesCastWordSourceSize?
                                targetSize sourceTy
                            some
                              (SolidCore.Solidity.Source.Expr.fixedBytesCast
                                targetSize sourceSize coreExpr)
                    | Ty.enum _ _ =>
                        -- Enum-typed target (e.g. a local `MyEnum c = MyEnum(x)`).
                        -- The operand is an enum value — either an
                        -- `enumFromUInt` conversion (which already range-checks
                        -- and Panic(0x21)s out of range) or another enum of the
                        -- same type. Enums are represented as their ordinal
                        -- word in core, so the lowered operand is stored as-is.
                        some coreExpr
                    | _ =>
                        if Ty.canImplicitlyConvert sourceTy targetTy then
                          some coreExpr
                        else
                          none
termination_by (sizeOf expr, 1)

def Expr.arrayLiteralCoreExprsAs? (storageNames : List Name)
    (targetTy : Ty) : List Expr -> Option (List CoreExpr)
  | [] => some []
  | expr :: rest => do
      let head ← Expr.toCoreAs? storageNames targetTy expr
      let tail ← Expr.arrayLiteralCoreExprsAs? storageNames targetTy rest
      some (head :: tail)
termination_by exprs => (sizeOf exprs, 2)

def Expr.arrayLiteralTy? (storageNames : List Name) :
    List Expr -> Option Ty
  | [] => none
  | first :: rest => do
      let exprs := first :: rest
      let elementTy ← Expr.arrayLiteralCommonTy? storageNames exprs
      some (Ty.array elementTy (some exprs.length))
termination_by exprs => (sizeOf exprs, 3)

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
  | Expr.member (Expr.typeName ty) "min" => do
      match Ty.uintBits? ty with
      | some _ => some ty
      | none =>
          match Ty.intBits? ty with
          | some _ => some ty
          | none => none
  | Expr.member (Expr.typeName ty) "max" => do
      match Ty.uintBits? ty with
      | some _ => some ty
      | none =>
          match Ty.intBits? ty with
          | some _ => some ty
          | none => none
  | Expr.newExpr Ty.bytes [Arg.positional _] => some Ty.bytes
  | Expr.newExpr Ty.string [Arg.positional _] => some Ty.string
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
      let rawTys ← Expr.abiDecodeSourceTypes? typesExpr
      -- solc forces each top-level decoded `address` component to
      -- `address payable` (TypeChecker.cpp:150-152); match it here so the
      -- lowered expression type agrees with the typechecker.
      let tys := rawTys.map (fun ty =>
        match ty with
        | Ty.address false => Ty.address true
        | _ => ty)
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
  | Expr.call (Expr.member (Expr.typeName Ty.bytes) "concat") _ =>
      some Ty.bytes
  | Expr.call (Expr.member (Expr.typeName Ty.string) "concat") _ =>
      some Ty.string
  | Expr.enumFromUInt _ _ => some (Ty.uint 8)
  | Expr.index base indexExpr => do
      let baseTy ← Expr.abiTy? storageNames base
      match Ty.fixedBytesSize? baseTy with
      | some _ => some (Ty.bytesN 1)
      | none =>
          match baseTy with
          | Ty.bytes => some (Ty.bytesN 1)
          | Ty.array elementTy _ => some elementTy
          | Ty.tuple elements => do
              let index ← Expr.numberLiteralNat? indexExpr
              listGet? elements index
          | Ty.struct _ elements => do
              let index ← Expr.numberLiteralNat? indexExpr
              listGet? elements index
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
  | expr@(Expr.ternary _ thenExpr elseExpr) =>
      -- A conditional of two untyped number literals carries the ternary's
      -- COMMON (mobile) type, not the then-branch's width nor `uint256`
      -- (solc `TypeChecker::visit(Conditional)`): `(t ? 63 : 255)` is `uint8`.
      match Expr.untypedLiteralMobileTy? expr with
      | some mobileTy => some mobileTy
      | none => do
          -- solc packs a conditional operand of `abi.encodePacked` using the
          -- ternary's COMMON (mobile) type, not the then-branch's width. Combine
          -- both branch types via `Ty.commonImplicit?`; fall back to the
          -- then-type when the else-branch type can't be inferred here.
          let thenTy ← Expr.abiTy? storageNames thenExpr
          match Expr.abiTy? storageNames elseExpr with
          | some elseTy => some ((Ty.commonImplicit? thenTy elseTy).getD thenTy)
          | none => some thenTy
  | Expr.tuple items => do
      let tys ←
        mapOption
          (fun item =>
            match item with
            | TupleItem.value
                (Expr.call (Expr.typeName ty) [Arg.positional _]) => do
                let _ ← Ty.toCore? ty
                some ty
            | TupleItem.value (Expr.typeName ty) => do
                let _ ← Ty.toCore? ty
                some ty
            | TupleItem.value _ => none
            | TupleItem.hole => none)
          items
      some (Ty.tuple tys)
  | Expr.array exprs => Expr.arrayLiteralTy? storageNames exprs
  | Expr.slice base _ _ => do
      let baseTy ← Expr.abiTy? storageNames base
      match baseTy with
      | Ty.bytes => some Ty.bytes
      | Ty.string => some Ty.string
      | Ty.array elementTy _ => some (Ty.array elementTy none)
      | _ => none
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

def Args.namedNamesForExternalCall? : List Arg -> Option (List Name)
  | [] => some []
  | Arg.named name _ :: rest => do
      let tail ← Args.namedNamesForExternalCall? rest
      some (name :: tail)
  | Arg.positional _ :: _ => none
termination_by args => (sizeOf args, 0)

def Args.toNamedExprsForNames? (paramNames : List Name)
    (args : List Arg) : Option (List Expr) := do
  let names ← Args.namedNamesForExternalCall? args
  if paramNames.length == args.length &&
      namesUnique names && namesUnique paramNames then
    mapOption (fun name => Args.findNamed? name args) paramNames
  else
    none

def ExternalCallKindEntry.namedArgExprs? (entry : ExternalCallKindEntry)
    (args : List Arg) : Option (List Expr) := do
  let paramNames ← mapOption (fun name? => name?) entry.paramNames
  if entry.paramTys.length == paramNames.length then
    Args.toNamedExprsForNames? paramNames args
  else
    none

-- ABIENCODE-LIT-FIXEDBYTES (#140): encode ONE argument against the callee's
-- DECLARED parameter type. The env-free `Expr.abiTy?` reports a literal's own
-- default type (a hex/string/bytes literal ⇒ dynamic `bytes`/`string`), but on a
-- call / `new C(...)` boundary solc encodes the argument by the PARAMETER type.
-- The only case where the produced BYTES (not merely the reported type) differ is
-- a string/hex/bytes literal targeting a fixed `bytesN`: solc emits ONE
-- left-aligned 32-byte word, never the dynamic head/length/data of `bytes`.
-- Re-encode that literal against the fixed target via
-- `Expr.toCoreFixedBytesLiteralAs?` — the SAME conversion TypeCheck already
-- accepts (`toCoreFixedBytesLiteralAs?` / `Literal.toFixedBytesWord?`).
--
-- Every other implicit conversion (number literal ⇒ `uintN`/`intN`, an exact
-- match, …) is byte-identical to the env-free encoding: a number literal's
-- `uint256` word equals its `uintN` word, so those keep the plain path — when the
-- arg's `abiTy?` already equals the parameter type, and otherwise
-- `toCoreFixedBytesLiteralAs?` returns `none` for non-`bytesN` targets so this
-- function returns `none` and the caller falls back to the env-free lowering
-- (whose bytes are already correct there). This mirrors solc's overload
-- resolution: any literal convertible to two distinct parameter types is
-- rejected by solc as ambiguous, so a lowered (accepted) call always has a
-- unique applicable signature.
def Expr.toAbiEncodeArgAgainst? (storageNames : List Name) (paramTy : Ty)
    (expr : Expr) : Option (CoreTy × CoreExpr) :=
  match Expr.abiTy? storageNames expr with
  | some ty =>
      if ty == paramTy then do
        let coreTy ← Ty.toCore? ty
        let coreExpr ← Expr.toCore? storageNames expr
        some (coreTy, coreExpr)
      else do
        let coreTy ← Ty.toCore? paramTy
        let coreExpr ← Expr.toCoreFixedBytesLiteralAs? paramTy expr
        some (coreTy, coreExpr)
  | none => none

-- Zip the DECLARED parameter types with the (already param-ordered, positional)
-- argument expressions, encoding each against its parameter type. Length
-- equality is enforced structurally (both lists must run out together).
def Args.toAbiEncodeAgainst? (storageNames : List Name) :
    List Ty -> List Arg -> Option (List CoreTy × List CoreExpr)
  | [], [] => some ([], [])
  | paramTy :: restTys, Arg.positional expr :: restArgs => do
      let (coreTy, coreExpr) ←
        Expr.toAbiEncodeArgAgainst? storageNames paramTy expr
      let (coreTys, coreExprs) ←
        Args.toAbiEncodeAgainst? storageNames restTys restArgs
      some (coreTy :: coreTys, coreExpr :: coreExprs)
  | _, _ => none

def ExternalCallKindEntry.toAbiCallSource? (storageNames : List Name)
    (entry : ExternalCallKindEntry) (args : List Arg) :
    Option (List Ty × List CoreTy × List CoreExpr) :=
  match Args.namedNamesForExternalCall? args with
  | some _ => do
      -- All-named (or empty) argument list: reorder to parameter order first,
      -- then encode each against its declared parameter type.
      let exprs ← ExternalCallKindEntry.namedArgExprs? entry args
      let positionalArgs := exprs.map Arg.positional
      let (coreTys, coreExprs) ←
        Args.toAbiEncodeAgainst? storageNames entry.paramTys positionalArgs
      some (entry.paramTys, coreTys, coreExprs)
  | none => do
      -- Positional argument list.
      let (coreTys, coreExprs) ←
        Args.toAbiEncodeAgainst? storageNames entry.paramTys args
      some (entry.paramTys, coreTys, coreExprs)

def ExternalCallKindEnv.lookupConstructorEntry?
    (env : ExternalCallKindEnv) (contractName : Name) :
    Option ExternalCallKindEntry :=
  match env with
  | [] => none
  | entry :: rest =>
      if entry.isConstructor && entry.contractName == contractName then
        some entry
      else
        ExternalCallKindEnv.lookupConstructorEntry? rest contractName

def ExternalCallKindEnv.lookupConstructorAbi? (storageNames : List Name)
    (env : ExternalCallKindEnv) (contractName : Name) (args : List Arg) :
    Option (List CoreTy × List CoreExpr) := do
  let entry ← ExternalCallKindEnv.lookupConstructorEntry? env contractName
  let (_, coreTys, coreExprs) ←
    ExternalCallKindEntry.toAbiCallSource? storageNames entry args
  some (coreTys, coreExprs)

def ExternalCallKindEnv.lookupAbiCall? (storageNames : List Name)
    (env : ExternalCallKindEnv) (contractName functionName : Name)
    (args : List Arg) :
    Option (ExternalCallKindEntry × List Ty × List CoreTy × List CoreExpr) :=
  match env with
  | [] => none
  | entry :: rest =>
      if !entry.isConstructor &&
          entry.contractName == contractName &&
          entry.functionName == functionName then
        match ExternalCallKindEntry.toAbiCallSource? storageNames entry args with
        | some (sourceTys, coreTys, coreExprs) =>
            some (entry, sourceTys, coreTys, coreExprs)
        | none =>
            ExternalCallKindEnv.lookupAbiCall?
              storageNames rest contractName functionName args
      else
        ExternalCallKindEnv.lookupAbiCall?
          storageNames rest contractName functionName args

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

def Expr.functionPointerSelectorCore? (storageNames : List Name)
    (functionPointer : Expr) (argTys : List Ty) : Option CoreExpr :=
  match functionPointer with
  | Expr.member _ name => do
      if name == "call" || name == "staticcall" ||
          name == "delegatecall" || name == "send" ||
          name == "transfer" then
        none
      else
        some ()
      let signature ← externalFunctionSignature? name argTys
      some
        (SolidCore.Solidity.Source.Expr.word
          (SolidCore.Solidity.Source.ABI.selectorFromSignature signature))
  | Expr.ident name =>
      let pointerCore := sourceIdentCore storageNames name
      some
        (SolidCore.Solidity.Source.Expr.externalFunctionSelector
          pointerCore)
  | _ => none

def Expr.externalCallKindForTarget (target : Expr) : CoreLowLevelCallKind :=
  match target with
  | Expr.ident name =>
      match generatedLibraryAddressName? name with
      | some _ => SolidCore.Solidity.Source.LowLevelCallKind.delegatecall
      | none => SolidCore.Solidity.Source.LowLevelCallKind.call
  | _ => SolidCore.Solidity.Source.LowLevelCallKind.call

def Expr.externalCallTargetContractNameWithEnv? (env : TypeEnv)
    (target : Expr) : Option Name :=
  match target with
  | Expr.ident targetName => do
      let ty ← TypeEnv.lookup? env targetName
      Ty.contractName? ty
  | Expr.call (Expr.typeName (Ty.user path)) [_] =>
      pathLast? path
  | _ => none

def lowLevelCallReservedMemberName (name : Name) : Bool :=
  name == "call" || name == "staticcall" ||
    name == "delegatecall" || name == "send" ||
    name == "transfer"

def highLevelExternalCallReservedMemberWithEnv
    (env : TypeEnv) (target : Expr) (name : Name) : Bool :=
  (lowLevelCallReservedMemberName name &&
      (Expr.externalCallTargetContractNameWithEnv? env target).isNone) ||
    Expr.memberCallIsBuiltin? target name

def Expr.externalCallKindForTargetWithEnv (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (target : Expr)
    (name : Name) (argTys : List Ty) : CoreLowLevelCallKind :=
  let defaultKind := Expr.externalCallKindForTarget target
  if defaultKind == SolidCore.Solidity.Source.LowLevelCallKind.delegatecall then
    defaultKind
  else
    match Expr.externalCallTargetContractNameWithEnv? env target with
    | some contractName =>
        match TypeEnv.lookupExternalCallKind?
            env contractName name argTys with
        | some kind => kind
        | none =>
            match ExternalCallKindEnv.lookupCallKind?
                externalCallKindEnv contractName name argTys with
            | some kind => kind
            | none => defaultKind
    | none => defaultKind

def Expr.externalCallMutabilityForTargetWithEnv (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (target : Expr)
    (name : Name) (argTys : List Ty) : Option StateMutability :=
  let defaultKind := Expr.externalCallKindForTarget target
  if defaultKind == SolidCore.Solidity.Source.LowLevelCallKind.delegatecall then
    none
  else
    match Expr.externalCallTargetContractNameWithEnv? env target with
    | some contractName =>
        match TypeEnv.lookupExternalMutability?
            env contractName name argTys with
        | some mutability => some mutability
        | none =>
            ExternalCallKindEnv.lookup?
              externalCallKindEnv contractName name argTys
    | none => none

def StateMutability.externalCallOptionsCore? (storageNames : List Name)
    (mutability? : Option StateMutability)
    (kind : CoreLowLevelCallKind) (options : List CallOption) :
    Option (CoreExpr × Option CoreExpr × Bool) :=
  if kind == SolidCore.Solidity.Source.LowLevelCallKind.delegatecall ||
      kind == SolidCore.Solidity.Source.LowLevelCallKind.staticcall then
    CallOptions.lowLevelDelegateGasCore? storageNames options
  else
    match mutability? with
    | some StateMutability.payable =>
        CallOptions.lowLevelCallValueGasCore? storageNames options
    | some StateMutability.nonpayable =>
        CallOptions.lowLevelDelegateGasCore? storageNames options
    | some StateMutability.view | some StateMutability.pure =>
        CallOptions.lowLevelDelegateGasCore? storageNames options
    | none =>
        CallOptions.lowLevelCallValueGasCore? storageNames options

def Expr.externalCallNeedsCodeCheckWithEnv (_env : TypeEnv)
    (returnTys : List Ty) : Expr -> Bool
  -- solc (v0.8.35, `ExpressionCompiler.cpp` `appendExternalFunctionCall`)
  -- emits the `extcodesize`/existence guard for every high-level external
  -- call whose `funKind` is `External`/`DelegateCall` (i.e. any contract/
  -- interface/library-typed receiver) when the ABI head size of the return
  -- types is 0 — i.e. exactly when there are NO return values (`encodedHeadSize
  -- == 0`).  With return values solc relies on its separate returndata-size
  -- check instead, so the extcodesize guard is skipped there.  The guard does
  -- NOT depend on the *shape* of the receiver expression: `contracts[i].f()`,
  -- `s.field.f()`, `m[k].f()` and `factory.get().f()` are all guarded exactly
  -- like an `ident` / `C(x)` receiver (gap A3).  Any member call reaching this
  -- point is already a high-level typed external call — low-level
  -- `.call`/`.staticcall`/`.delegatecall`/`.send`/`.transfer` are filtered out
  -- upstream by `toExternalCallWithKindEnv?`, so no code check is emitted for
  -- them.
  | Expr.call (Expr.member _ _) _ => returnTys.isEmpty
  | Expr.callWithOptions (Expr.member _ _) _ _ => returnTys.isEmpty
  | _ => false

/-- A storage lvalue CoreExpr (already lowered by `Expr.toCore?`) rooted at a
    top-level STATE variable, decomposed into `(name, indexes)` — the same
    `(name, indexes)` the value forms `storageIndex`/`storagePath` load from.
    Mapping-value / array-element / struct-member storage pointers lower to
    `storageIndex name idx`, a nested `index` chain over one of those, or a bare
    `storage name`; struct members were already rewritten to an index ordinal
    upstream (`resolveStructs`). Used to recover the slot path for
    `coreStoragePointerSlotExpr?`. -/
def coreStorageStatePath? : CoreExpr -> Option (Name × List CoreExpr)
  | SolidCore.Solidity.Source.Expr.storage name => some (name, [])
  | SolidCore.Solidity.Source.Expr.storageIdent name => some (name, [])
  | SolidCore.Solidity.Source.Expr.storageIndex name idx => some (name, [idx])
  | SolidCore.Solidity.Source.Expr.storagePath name indexes => some (name, indexes)
  | SolidCore.Solidity.Source.Expr.index base idx => do
      let (name, indexes) ← coreStorageStatePath? base
      some (name, indexes ++ [idx])
  | _ => none

/-- A storage lvalue CoreExpr rooted at a `T storage` LOCAL pointer, decomposed
    into `(name, indexes)`. A bare storage-pointer local lowers to `Expr.var
    name`; further element access lowers to an `index` chain over it. Used to
    recover the slot of a storage-pointer-local argument. -/
def coreStorageRefPath? : CoreExpr -> Option (Name × List CoreExpr)
  | SolidCore.Solidity.Source.Expr.var name => some (name, [])
  | SolidCore.Solidity.Source.Expr.index base idx => do
      let (name, indexes) ← coreStorageRefPath? base
      some (name, indexes ++ [idx])
  | _ => none

/-- The slot-word core expression for a `storage`-pointer library-call
    argument. solc encodes a `T storage self` parameter as its storage slot
    number in the delegatecall calldata. A plain top-level state-variable
    reference lowers (via `Args.toAbiEncodeSource?`) to `Expr.storage name`; its
    slot is the compile-time-constant `Expr.storageSlot name`. Other
    storage-pointer shapes — a `mapping` value, an array element, a struct-member
    array (all rooted at a state variable, possibly through a nested `index`
    chain), or a `T storage` local pointer — carry a runtime-computed slot; those
    are encoded via `storagePathSlot` / `storageRefSlot`, which resolve the same
    slot the value forms load from (`State.resolveStoragePathSlot`). Only a shape
    that is neither a state-rooted nor a local-rooted storage lvalue is left
    over-rejecting (`none`). -/
def coreStoragePointerSlotExpr? : CoreExpr -> Option CoreExpr
  | SolidCore.Solidity.Source.Expr.storage name =>
      some (SolidCore.Solidity.Source.Expr.storageSlot name)
  | SolidCore.Solidity.Source.Expr.storageIdent name =>
      some (SolidCore.Solidity.Source.Expr.storageSlot name)
  | coreExpr =>
      match coreStorageStatePath? coreExpr with
      | some (name, indexes) =>
          some (SolidCore.Solidity.Source.Expr.storagePathSlot name indexes)
      | none =>
          match coreStorageRefPath? coreExpr with
          | some (name, indexes) =>
              some (SolidCore.Solidity.Source.Expr.storageRefSlot name indexes)
          | none => none

/-- Rewrite the ABI types/expressions of a library external call so each
    `storage`-location parameter is encoded by SLOT (`uint256`), matching solc's
    delegatecall calldata. Non-storage parameters pass through unchanged.
    Returns `none` (over-reject) if a `storage` argument is not a slot-encodable
    top-level state-variable reference. -/
def applyStoragePointerCallArgs? :
    List CoreTy -> List CoreExpr -> List (Option DataLocation) ->
      Option (List CoreTy × List CoreExpr)
  | [], [], _ => some ([], [])
  | coreTy :: coreTys, coreExpr :: coreExprs, locs => do
      let (tailTys, tailExprs) ←
        applyStoragePointerCallArgs? coreTys coreExprs locs.tail
      if dataLocationIsStorage (locs.headD none) then
        let slotExpr ← coreStoragePointerSlotExpr? coreExpr
        some
          ( SolidCore.Solidity.Source.Ty.uint256 :: tailTys
          , slotExpr :: tailExprs )
      else
        some (coreTy :: tailTys, coreExpr :: tailExprs)
  | _, _, _ => none

/-- The library external ABI/signature payload with the `storage`-pointer slot
    lowering applied. When no parameter is a `storage` pointer this is exactly
    `(externalFunctionSignature?, coreTys, coreExprs)` — no behaviour change for
    ordinary contract calls and memory/calldata library calls. -/
def externalCallStoragePointerPayload?
    (name : Name) (sourceTys : List Ty) (coreTys : List CoreTy)
    (coreExprs : List CoreExpr) (locations : List (Option DataLocation))
    (librarySignature? : Option String := none) :
    Option (String × List CoreTy × List CoreExpr) := do
  -- BUG#6: a public/external LIBRARY delegatecall hashes the
  -- library-qualified signature carried by its `ExternalCallKindEntry`;
  -- ordinary contract calls keep the external-ABI signature.
  let signature ←
    match librarySignature? with
    | some signature => some signature
    | none =>
        externalFunctionSignatureWithLocations? name sourceTys locations
  if locations.any dataLocationIsStorage then
    let (encTys, encExprs) ←
      applyStoragePointerCallArgs? coreTys coreExprs locations
    some (signature, encTys, encExprs)
  else
    some (signature, coreTys, coreExprs)

/-- The target contract/library name for the ABI/kind-env lookup: a regular
    contract-typed receiver via the type env, OR a generated library-address
    ident (`__solidcore_library_*`, produced by the using-for / direct library
    call rewrites) mapped back to its library name. The latter is what lets a
    public/external LIBRARY call consult its `ExternalCallKindEntry` (carrying
    the parameters' data locations) so a `storage`-pointer `self` is encoded by
    slot. Contract receivers already resolve through
    `externalCallTargetContractNameWithEnv?`; recovering the library name here
    does NOT change kind/mutability resolution (those keep using
    `externalCallTargetContractNameWithEnv?`, for which a generated library
    address still resolves to `delegatecall` by shape). -/
def Expr.externalCallAbiContractName? (env : TypeEnv) (target : Expr) :
    Option Name :=
  match Expr.externalCallTargetContractNameWithEnv? env target with
  | some contractName => some contractName
  | none =>
      match target with
      | Expr.ident targetName => generatedLibraryAddressName? targetName
      | _ => none

/-- WS1 (H, external-call args): rewrite the lowered ABI argument cores of an
    all-positional call through `argEnvLower` (the env-aware argument lowerer;
    it declines with `none` for every unflagged argument, keeping the env-less
    core byte-identically). Positional-only: named arguments are reordered by
    the ABI lookup, so the source-to-core zip would misalign — callers gate on
    `Args.allPositional`. -/
def Args.applyArgEnvLowerToCallArgCores
    (argEnvLower : Ty -> Expr -> Option CoreExpr) :
    List Arg -> List Ty -> List CoreExpr -> List CoreExpr
  | Arg.positional expr :: args, ty :: tys, core :: cores =>
      ((argEnvLower ty expr).getD core) ::
        Args.applyArgEnvLowerToCallArgCores argEnvLower args tys cores
  | _ :: args, _ :: tys, core :: cores =>
      core :: Args.applyArgEnvLowerToCallArgCores argEnvLower args tys cores
  | _, _, cores => cores

def Args.allPositional (args : List Arg) : Bool :=
  args.all (fun arg =>
    match arg with
    | Arg.positional _ => true
    | Arg.named _ _ => false)

def Expr.externalCallAbiWithKindEnv? (storageNames : List Name)
    (env : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv)
    (target : Expr) (name : Name) (args : List Arg)
    (argEnvLower : Ty -> Expr -> Option CoreExpr := fun _ _ => none) :
    Option (List Ty × List CoreTy × List CoreExpr ×
      List (Option DataLocation) × Option String) :=
  let applyEnv := fun (sourceTys : List Ty) (coreExprs : List CoreExpr) =>
    if Args.allPositional args then
      Args.applyArgEnvLowerToCallArgCores argEnvLower args sourceTys coreExprs
    else
      coreExprs
  let fallback :=
    match Args.toAbiEncodeSource? storageNames args with
    | some (sourceTys, coreTys, coreExprs) =>
        some (sourceTys, coreTys, applyEnv sourceTys coreExprs,
          ([] : List (Option DataLocation)), (none : Option String))
    | none => none
  match Expr.externalCallAbiContractName? env target with
  | some contractName =>
      match
          ExternalCallKindEnv.lookupAbiCall?
            storageNames externalCallKindEnv contractName name args with
      | some (entry, sourceTys, coreTys, coreExprs) =>
          -- BUG#6: surface the entry's library-qualified signature so the
          -- delegatecall payload hashes it (contract entries carry `none`).
          some (sourceTys, coreTys, applyEnv sourceTys coreExprs,
            entry.paramLocations, entry.librarySignature?)
      | none => fallback
  | none => fallback

def Expr.toExternalCallWithKindEnv? (storageNames : List Name)
    (env : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv)
    (argEnvLower : Ty -> Expr -> Option CoreExpr := fun _ _ => none) :
    Expr ->
      Option
        (CoreLowLevelCallKind × CoreExpr × CoreExpr × CoreExpr ×
          Option CoreExpr × Bool)
  | Expr.call (Expr.member target name) args => do
      if highLevelExternalCallReservedMemberWithEnv env target name then
        none
      else
        some ()
      let targetCore ← Expr.toCore? storageNames target
      let (sourceTys, coreTys, coreExprs, locations, librarySignature?) ←
        Expr.externalCallAbiWithKindEnv?
          storageNames env externalCallKindEnv target name args
          (argEnvLower := argEnvLower)
      let kind :=
        Expr.externalCallKindForTargetWithEnv
          env externalCallKindEnv target name sourceTys
      let (signature, encTys, encExprs) ←
        externalCallStoragePointerPayload? name sourceTys coreTys coreExprs
          locations (librarySignature? := librarySignature?)
      let callData :=
        SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
          (SolidCore.Solidity.Source.Expr.word
            (SolidCore.Solidity.Source.ABI.selectorFromSignature signature))
          encTys encExprs
      some
        ( kind
        , targetCore
        , callData
        , SolidCore.Solidity.Source.Expr.word 0
        , none
        , false )
  | Expr.callWithOptions (Expr.member target name) options args => do
      if highLevelExternalCallReservedMemberWithEnv env target name then
        none
      else
        some ()
      let targetCore ← Expr.toCore? storageNames target
      let (sourceTys, coreTys, coreExprs, locations, librarySignature?) ←
        Expr.externalCallAbiWithKindEnv?
          storageNames env externalCallKindEnv target name args
          (argEnvLower := argEnvLower)
      let kind :=
        Expr.externalCallKindForTargetWithEnv
          env externalCallKindEnv target name sourceTys
      let mutability? :=
        Expr.externalCallMutabilityForTargetWithEnv
          env externalCallKindEnv target name sourceTys
      let (valueCore, gasCore?, gasFirst) ←
        StateMutability.externalCallOptionsCore?
          storageNames mutability? kind options
      let (signature, encTys, encExprs) ←
        externalCallStoragePointerPayload? name sourceTys coreTys coreExprs
          locations (librarySignature? := librarySignature?)
      let callData :=
        SolidCore.Solidity.Source.Expr.abiEncodeWithSelector
          (SolidCore.Solidity.Source.Expr.word
            (SolidCore.Solidity.Source.ABI.selectorFromSignature signature))
          encTys encExprs
      some (kind, targetCore, callData, valueCore, gasCore?, gasFirst)
  | _ => none

def Expr.externalCallDeclaredReturnTysWithKindEnv?
    (storageNames : List Name) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) : Expr -> Option (List Ty)
  | Expr.call (Expr.member target name) args => do
      let contractName ← Expr.externalCallTargetContractNameWithEnv? env target
      let (entry, _, _, _) ←
        ExternalCallKindEnv.lookupAbiCall?
          storageNames externalCallKindEnv contractName name args
      some entry.returnTys
  | Expr.callWithOptions (Expr.member target name) _ args => do
      let contractName ← Expr.externalCallTargetContractNameWithEnv? env target
      let (entry, _, _, _) ←
        ExternalCallKindEnv.lookupAbiCall?
          storageNames externalCallKindEnv contractName name args
      some entry.returnTys
  | _ => none

def Expr.toExternalCallWithTypeEnv? (storageNames : List Name)
    (env : TypeEnv) : Expr ->
      Option
        (CoreLowLevelCallKind × CoreExpr × CoreExpr × CoreExpr ×
          Option CoreExpr × Bool) :=
  Expr.toExternalCallWithKindEnv? storageNames env []

def Expr.toExternalCall? (storageNames : List Name) :
    Expr ->
      Option
        (CoreLowLevelCallKind × CoreExpr × CoreExpr × CoreExpr ×
          Option CoreExpr × Bool) :=
  Expr.toExternalCallWithKindEnv? storageNames [] []

-- The trailing `Bool` is `valueBeforeSalt` — the source order of the creation
-- options, threaded into `Expr.contractCreate` (DIV-CREATE-2).
def Expr.toContractCreationWithKindEnv? (storageNames : List Name)
    (externalCallKindEnv : ExternalCallKindEnv) :
    Expr -> Option (Name × CoreExpr × CoreExpr × Option CoreExpr × Bool)
  | Expr.newExpr ty args => do
      let contractName ← Ty.contractName? ty
      let (coreTys, coreExprs) ←
        match
            ExternalCallKindEnv.lookupConstructorEntry?
              externalCallKindEnv contractName with
        | some _ =>
            ExternalCallKindEnv.lookupConstructorAbi?
              storageNames externalCallKindEnv contractName args
        | none => Args.toAbiEncode? storageNames args
      some
        ( contractName
        , SolidCore.Solidity.Source.Expr.abiEncode coreTys coreExprs
        , SolidCore.Solidity.Source.Expr.word 0
        , none
        , true )
  | Expr.callWithOptions (Expr.newExpr ty []) options args => do
      let contractName ← Ty.contractName? ty
      let (value?, salt?, valueBeforeSalt) ←
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
      let (coreTys, coreExprs) ←
        match
            ExternalCallKindEnv.lookupConstructorEntry?
              externalCallKindEnv contractName with
        | some _ =>
            ExternalCallKindEnv.lookupConstructorAbi?
              storageNames externalCallKindEnv contractName args
        | none => Args.toAbiEncode? storageNames args
      some
        ( contractName
        , SolidCore.Solidity.Source.Expr.abiEncode coreTys coreExprs
        , valueCore
        , saltCore?
        , valueBeforeSalt )
  | _ => none

def Expr.toContractCreation? (storageNames : List Name) :
    Expr -> Option (Name × CoreExpr × CoreExpr × Option CoreExpr × Bool) :=
  Expr.toContractCreationWithKindEnv? storageNames []

def Expr.toContractCreationCoreWithKindEnv? (storageNames : List Name)
    (externalCallKindEnv : ExternalCallKindEnv) (expr : Expr) :
    Option CoreExpr := do
  let (contractName, argsCore, valueCore, saltCore?, valueBeforeSalt) ←
    Expr.toContractCreationWithKindEnv?
      storageNames externalCallKindEnv expr
  some
    (SolidCore.Solidity.Source.Expr.contractCreate
      contractName argsCore valueCore saltCore? valueBeforeSalt)

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

def CoreBindingDecls.toVarExprsAs
    (tys : List Ty) (bindings : List CoreBindingDecl) : List CoreExpr :=
  (tys.zip bindings).map (fun pair =>
    Ty.implicitCleanupCore pair.fst
      (SolidCore.Solidity.Source.Expr.var pair.snd.name))

def CoreBindingDecls.assignToVars (names : List Name)
    (bindings : List CoreBindingDecl) : List CoreStmt :=
  (names.zip bindings).map
    (fun pair =>
      SolidCore.Solidity.Source.Stmt.assign
        (SolidCore.Solidity.Source.LValue.var pair.fst)
        (SolidCore.Solidity.Source.Expr.var pair.snd.name))

def CoreBindingDecls.assignToVarsAs (tys : List Ty) (names : List Name)
    (bindings : List CoreBindingDecl) : List CoreStmt :=
  (names.zip (tys.zip bindings)).map
    (fun pair =>
      SolidCore.Solidity.Source.Stmt.assign
        (SolidCore.Solidity.Source.LValue.var pair.fst)
        (Ty.implicitCleanupCore pair.snd.fst
          (SolidCore.Solidity.Source.Expr.var pair.snd.snd.name)))

def CoreBindingDecls.assignToTargets
    (targets : List (Option CoreLValue))
    (bindings : List CoreBindingDecl) : List CoreStmt :=
  (targets.zip bindings).filterMap
    (fun pair =>
      match pair.fst with
      | some target =>
          some
            (SolidCore.Solidity.Source.Stmt.assign target
              (SolidCore.Solidity.Source.Expr.var pair.snd.name))
      | none => none)

def Expr.transferCore? (storageNames : List Name)
    (target value : Expr) : Option CoreStmt := do
  let targetCore ← Expr.toCore? storageNames target
  let valueCore ← Expr.toCore? storageNames value
  some
    (SolidCore.Solidity.Source.Stmt.tryExternalCall
      SolidCore.Solidity.Source.LowLevelCallKind.call
      targetCore
      (SolidCore.Solidity.Source.Expr.byteArray [])
      valueCore
      (some (SolidCore.Solidity.Source.Expr.word 2300))
      false false [] [] SolidCore.Solidity.Source.Stmt.skip [])

def Expr.externalCallWithReturnsCoreWithKindEnv? (storageNames : List Name)
    (env : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv)
    (namePrefix : String) (returnTys : List Ty) (expr : Expr)
    (successBody : List CoreBindingDecl -> CoreStmt)
    (argEnvLower : Ty -> Expr -> Option CoreExpr := fun _ _ => none) :
    Option CoreStmt := do
  let (kind, targetCore, calldataCore, valueCore, gasCore?, gasFirst) ←
    Expr.toExternalCallWithKindEnv? storageNames env externalCallKindEnv
      (argEnvLower := argEnvLower) expr
  let callReturnTys :=
    (Expr.externalCallDeclaredReturnTysWithKindEnv?
      storageNames env externalCallKindEnv expr).getD returnTys
  if callReturnTys.length != returnTys.length then
    none
  else
    some ()
  let returnBindings ← Tys.toExternalReturnBindings? namePrefix callReturnTys
  let returnAbiCleanups ← Tys.toCoreAbiCleanups? callReturnTys
  let checkTargetCode :=
    Expr.externalCallNeedsCodeCheckWithEnv env callReturnTys expr
  some
    (SolidCore.Solidity.Source.Stmt.tryExternalCall
      kind targetCore calldataCore valueCore gasCore? gasFirst
      checkTargetCode returnBindings returnAbiCleanups
      (successBody returnBindings) [])

def Expr.externalCallWithReturnsCoreWithTypeEnv? (storageNames : List Name)
    (env : TypeEnv)
    (namePrefix : String) (returnTys : List Ty) (expr : Expr)
    (successBody : List CoreBindingDecl -> CoreStmt) : Option CoreStmt :=
  Expr.externalCallWithReturnsCoreWithKindEnv?
    storageNames env [] namePrefix returnTys expr successBody

def Expr.externalCallWithReturnsCore? (storageNames : List Name)
    (namePrefix : String) (returnTys : List Ty) (expr : Expr)
    (successBody : List CoreBindingDecl -> CoreStmt) : Option CoreStmt :=
  Expr.externalCallWithReturnsCoreWithKindEnv?
    storageNames [] [] namePrefix returnTys expr successBody

def Expr.externalCallDiscardCoreWithKindEnv? (storageNames : List Name)
    (env : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv)
    (expr : Expr)
    (argEnvLower : Ty -> Expr -> Option CoreExpr := fun _ _ => none) :
    Option CoreStmt :=
  Expr.externalCallWithReturnsCoreWithKindEnv?
    (argEnvLower := argEnvLower)
    storageNames env externalCallKindEnv "__ext" [] expr
    (fun _ => SolidCore.Solidity.Source.Stmt.skip)

def Expr.externalCallDiscardCoreWithTypeEnv? (storageNames : List Name)
    (env : TypeEnv) (expr : Expr) : Option CoreStmt :=
  Expr.externalCallDiscardCoreWithKindEnv? storageNames env [] expr

def Expr.externalCallDiscardCore? (storageNames : List Name)
    (expr : Expr) : Option CoreStmt :=
  Expr.externalCallDiscardCoreWithKindEnv? storageNames [] [] expr

def Expr.externalCallSingleReturnCoreWithKindEnv? (storageNames : List Name)
    (env : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv)
    (expectedTy : Ty) (expr : Expr) (useResult : CoreExpr -> CoreStmt)
    (argEnvLower : Ty -> Expr -> Option CoreExpr := fun _ _ => none) :
    Option CoreStmt := do
  Expr.externalCallWithReturnsCoreWithKindEnv?
    (argEnvLower := argEnvLower)
    storageNames env externalCallKindEnv "__ext" [expectedTy] expr
    (fun bindings =>
      match bindings with
      | [binding] =>
          useResult
            (Ty.implicitCleanupCore expectedTy
              (SolidCore.Solidity.Source.Expr.var binding.name))
      | _ => SolidCore.Solidity.Source.Stmt.skip)

def Expr.externalCallSingleReturnCoreWithTypeEnv? (storageNames : List Name)
    (env : TypeEnv) (expectedTy : Ty) (expr : Expr)
    (useResult : CoreExpr -> CoreStmt) : Option CoreStmt :=
  Expr.externalCallSingleReturnCoreWithKindEnv?
    storageNames env [] expectedTy expr useResult

def Expr.externalCallSingleReturnCore? (storageNames : List Name)
    (expectedTy : Ty) (expr : Expr) (useResult : CoreExpr -> CoreStmt) :
    Option CoreStmt := do
  Expr.externalCallSingleReturnCoreWithKindEnv?
    storageNames [] [] expectedTy expr useResult

def Expr.externalCallAssignVarsCoreWithKindEnv? (storageNames : List Name)
    (env : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv)
    (returnTys : List Ty) (targetNames : List Name) (expr : Expr)
    (argEnvLower : Ty -> Expr -> Option CoreExpr := fun _ _ => none) :
    Option CoreStmt := do
  if targetNames.length == returnTys.length then
    Expr.externalCallWithReturnsCoreWithKindEnv?
      (argEnvLower := argEnvLower)
      storageNames env externalCallKindEnv "__ext" returnTys expr
      (fun bindings =>
        SolidCore.Solidity.Source.Stmt.block
          (CoreBindingDecls.assignToVarsAs returnTys targetNames bindings))
  else
    none

def Expr.externalCallAssignVarsCoreWithTypeEnv? (storageNames : List Name)
    (env : TypeEnv) (returnTys : List Ty) (targetNames : List Name)
    (expr : Expr) : Option CoreStmt :=
  Expr.externalCallAssignVarsCoreWithKindEnv?
    storageNames env [] returnTys targetNames expr

def Expr.externalCallAssignVarsCore? (storageNames : List Name)
    (returnTys : List Ty) (targetNames : List Name) (expr : Expr) :
    Option CoreStmt := do
  Expr.externalCallAssignVarsCoreWithKindEnv?
    storageNames [] [] returnTys targetNames expr

def Expr.externalCallReturnCoreWithKindEnv? (storageNames : List Name)
    (env : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv)
    (returnTys : List Ty) (expr : Expr)
    (argEnvLower : Ty -> Expr -> Option CoreExpr := fun _ _ => none) :
    Option CoreStmt :=
  Expr.externalCallWithReturnsCoreWithKindEnv?
    (argEnvLower := argEnvLower)
    storageNames env externalCallKindEnv "__extret" returnTys expr
    (fun bindings =>
      SolidCore.Solidity.Source.Stmt.returnValues
        (CoreBindingDecls.toVarExprsAs returnTys bindings))

def Expr.externalCallReturnCoreWithTypeEnv? (storageNames : List Name)
    (env : TypeEnv) (returnTys : List Ty) (expr : Expr) : Option CoreStmt :=
  Expr.externalCallReturnCoreWithKindEnv? storageNames env [] returnTys expr

def Expr.externalCallReturnCore? (storageNames : List Name)
    (returnTys : List Ty) (expr : Expr) : Option CoreStmt :=
  Expr.externalCallReturnCoreWithKindEnv? storageNames [] [] returnTys expr

def TupleItems.toAbiDecodeSourceTypes? :
    List TupleItem -> Option (List Ty)
  | [] => some []
  | TupleItem.value (Expr.typeName ty) :: rest => do
      let _ ← Ty.toCore? ty
      let tail ← TupleItems.toAbiDecodeSourceTypes? rest
      some (ty :: tail)
  | _ => none
termination_by items => (sizeOf items, 0)

-- The second argument to `abi.decode` must be a TUPLE of types
-- (solc `TypeChecker.cpp:127-136`, error 6444). A bare single type
-- `abi.decode(data, uint)` is rejected; `(uint)` (a one-element tuple) is
-- accepted. The importer preserves the tuple wrapper for this argument, so the
-- only accepted shape is `Expr.tuple`.
def Expr.abiDecodeSourceTypes? : Expr -> Option (List Ty)
  | Expr.tuple items => TupleItems.toAbiDecodeSourceTypes? items
  | _ => none

def Expr.toAbiDecode? (storageNames : List Name)
    (data typesExpr : Expr) :
    Option (List CoreTy × List CoreAbiCleanup × CoreExpr) := do
  let sourceTys ← Expr.abiDecodeSourceTypes? typesExpr
  let coreTys ← Ty.listToCore? sourceTys
  let cleanups ← Tys.toCoreAbiCleanups? sourceTys
  -- R3 (#192): `abi.decode`'s DATA argument is a VALUE-USE boundary (it consumes
  -- the byte CONTENTS), exactly like `abi.encode*`/`keccak256`/`bytes.concat`. A
  -- bare state `bytes`/`string` lowers to `Expr.storage key`, whose eval is the
  -- HEADER word (the `.length` convention), so an unmaterialized decode target
  -- fed the header word to `asBytes?` → `none` → Panic(0) instead of decoding
  -- the stored contents. Materialize the bare-storage core so the full contents
  -- are read (solc implicitly copies a storage bytes/string to memory before
  -- `abi.decode`); every other core shape passes through untouched.
  let dataCore ← Expr.toCore? storageNames data
  some (coreTys, cleanups, dataCore)
termination_by (sizeOf data + sizeOf typesExpr + 1, 1)

def Expr.toCoreLValue? (storageNames : List Name) : Expr -> Option CoreLValue
  | Expr.ident name =>
      match stateNameRuntimeKey? name storageNames with
      | some key => some (SolidCore.Solidity.Source.LValue.storage key)
      | none =>
          match stateNameImmutableKey? name storageNames with
          | some key => some (SolidCore.Solidity.Source.LValue.immutable key)
          | none => some (SolidCore.Solidity.Source.LValue.var name)
  | Expr.index (Expr.ident name) index =>
      match stateNameRuntimeKey? name storageNames with
      | some key =>
        do
        let indexCore ← Expr.toCore? storageNames index
        -- R3 (#192): mapping/array WRITE index key — same value-use boundary as
        -- the read arm; materialize a bare-storage key so `m[stateStr] = v` hits
        -- the contents-derived slot (scalar keys load identically).
        some (SolidCore.Solidity.Source.LValue.storageIndex key
          indexCore)
      | none =>
        do
        let baseCore ← Expr.toCoreLValue? storageNames (Expr.ident name)
        let indexCore ← Expr.toCore? storageNames index
        some (SolidCore.Solidity.Source.LValue.index baseCore indexCore)
  | Expr.index base index => do
      let baseCore ← Expr.toCoreLValue? storageNames base
      let indexCore ← Expr.toCore? storageNames index
      some (SolidCore.Solidity.Source.LValue.index baseCore indexCore)
  | Expr.ternary cond thenExpr elseExpr => do
      let condCore ← Expr.toCore? storageNames cond
      let thenTarget ← Expr.toCoreLValue? storageNames thenExpr
      let elseTarget ← Expr.toCoreLValue? storageNames elseExpr
      some
        (SolidCore.Solidity.Source.LValue.ternary
          condCore thenTarget elseTarget)
  | Expr.member (Expr.typeName (Ty.user _)) name =>
      -- Qualified (inherited) STATE-VARIABLE write target (`Base.v = …`):
      -- resolves to the same storage/immutable slot as the bare identifier.
      match stateNameRuntimeKey? name storageNames with
      | some key => some (SolidCore.Solidity.Source.LValue.storage key)
      | none =>
          match stateNameImmutableKey? name storageNames with
          | some key => some (SolidCore.Solidity.Source.LValue.immutable key)
          | none => none
  | Expr.call (Expr.typeName Ty.bytes) [Arg.positional inner]
  | Expr.call (Expr.typeName Ty.string) [Arg.positional inner] =>
      -- `bytes(x)`/`string(x)` as an assignment TARGET (`bytes(m)[i] = v`): the
      -- string<->bytes conversion is a pointer reinterpret (identical layout),
      -- so the conversion is transparent for lvalue resolution — peel it and
      -- lower the operand as an lvalue. The typechecker has already confirmed
      -- the operand is a dynamic `bytes`/`string` lvalue.
      Expr.toCoreLValue? storageNames inner
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
          let head :=
            if binding.location == some DataLocation.memory then
              SolidCore.Solidity.Source.Stmt.memoryVarDecl coreTy name none
            else
              SolidCore.Solidity.Source.Stmt.varDecl coreTy name none
          some (head :: tail)
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

-- Is any LHS component itself a parenthesized sub-tuple? (`((a, b), c) = …`)
def TupleItems.hasNestedTuple : List TupleItem -> Bool
  | [] => false
  | TupleItem.value (Expr.tuple _) :: _ => true
  | _ :: rest => TupleItems.hasNestedTuple rest
termination_by items => sizeOf items

-- Elaborate one (possibly nested) tuple-assignment LHS component to a core
-- `TupleTarget`. A parenthesized sub-tuple recurses; a `hole` maps to `hole`;
-- everything else must be an assignable core lvalue.
def TupleItem.toCoreTupleTarget? (storageNames : List Name) :
    TupleItem -> Option CoreTupleTarget
  | TupleItem.hole => some SolidCore.Solidity.Source.TupleTarget.hole
  | TupleItem.value (Expr.tuple innerItems) => do
      let inner ← TupleItems.toCoreTupleTargets? storageNames innerItems
      some (SolidCore.Solidity.Source.TupleTarget.nested inner)
  | TupleItem.value expr => do
      let target ← Expr.toCoreLValue? storageNames expr
      some (SolidCore.Solidity.Source.TupleTarget.leaf target)
termination_by item => (sizeOf item, 0)

def TupleItems.toCoreTupleTargets? (storageNames : List Name) :
    List TupleItem -> Option (List CoreTupleTarget)
  | [] => some []
  | item :: rest => do
      let head ← TupleItem.toCoreTupleTarget? storageNames item
      let tail ← TupleItems.toCoreTupleTargets? storageNames rest
      some (head :: tail)
termination_by items => (sizeOf items, 1)

def tupleAssignmentCore? (storageNames : List Name)
    (lhsItems : List TupleItem) (rhs : Expr) : Option CoreStmt :=
  if TupleItems.hasNestedTuple lhsItems then do
    -- Nested LHS: `((a, b), c) = ((x, y), z)`. solc accepts these; the RHS is
    -- evaluated once and destructured against the nested target tree in
    -- lockstep, matching solc's left-to-right component semantics. The flat
    -- `assignTuple` path is unchanged for non-nested LHSs.
    let targets ← TupleItems.toCoreTupleTargets? storageNames lhsItems
    let rhsCore ← Expr.toCore? storageNames rhs
    some (SolidCore.Solidity.Source.Stmt.assignTupleNested targets rhsCore)
  else do
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

-- GENERAL TUPLE-VARDECL lowering (#171 abi.decode RHS, #172 ternary RHS, and the
-- general vein): a multi-binding tuple variable DECLARATION `(T1 a, …, Tn z) =
-- rhs` for ANY initializer `rhs`. solc accepts these and binds each declared
-- local to the corresponding component of the tuple-typed RHS; an omitted
-- component (`(uint x, ) = …`, `(, uint y) = …`) is a skipped binding. The
-- literal-tuple decl path (`(some (Expr.tuple items))`) and the internal-call
-- CALL-shaped RHS arms are handled by dedicated arms; every other RHS — an
-- `abi.decode` member call, a ternary of tuples, etc. — was missed at
-- DECLARATION position (only the RETURN and tuple-ASSIGNMENT positions were
-- handled), so replay yielded `TypeError.unsupported`. This mirrors the
-- tuple-ASSIGNMENT path (`tupleAssignmentCore?`), which already lowers ANY RHS
-- via `Expr.toCore?` then `assignTuple`: declare the fresh locals
-- (`VarBindings.toCoreTupleDecls?`, dropping anonymous components), then bind the
-- components through `assignTuple` with the RHS lowered by `Expr.toCore?` (which
-- carries any per-component cleanups, e.g. abi.decode's). The binding count
-- equals the RHS component arity (enforced by the acceptance predicate), so the
-- targets line up with the components. Returns `none` if the RHS is not
-- lowerable by `Expr.toCore?` (e.g. it nests internal calls), so callers can
-- fall back to their existing hoisting logic.
def tupleVarDeclGeneralCorePieces? (storageNames : List Name)
    (bindings : List VarBinding) (rhs : Expr) :
    Option (List CoreStmt × List CoreStmt) := do
  let coreDecls ← VarBindings.toCoreTupleDecls? bindings
  let targets ← VarBindings.toCoreTupleTargets? bindings
  let rhsCore ← Expr.toCore? storageNames rhs
  some
    ( coreDecls
    , [SolidCore.Solidity.Source.Stmt.assignTuple targets rhsCore] )

def VarBindings.assignFromExternalReturnBindings? :
    List VarBinding -> List CoreBindingDecl -> Option (List CoreStmt)
  | [], [] => some []
  | binding :: bindings, ret :: returns => do
      let tail ←
        VarBindings.assignFromExternalReturnBindings? bindings returns
      match binding.name with
      | none => some tail
      | some name =>
          match binding.ty with
          | some ty =>
              some
                (SolidCore.Solidity.Source.Stmt.assign
                  (SolidCore.Solidity.Source.LValue.var name)
                  (Ty.implicitCleanupCore ty
                    (SolidCore.Solidity.Source.Expr.var ret.name)) :: tail)
          | none => none
  | _, _ => none

def VarBindings.sourceTysIncludingAnonymous? :
    List VarBinding -> Option (List Ty)
  | [] => some []
  | binding :: rest => do
      let ty ← binding.ty
      let tail ← VarBindings.sourceTysIncludingAnonymous? rest
      some (ty :: tail)

def Expr.externalCallAssignBindingsCorePiecesWithKindEnv?
    (storageNames : List Name) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (bindings : List VarBinding) (expr : Expr)
    (argEnvLower : Ty -> Expr -> Option CoreExpr := fun _ _ => none) :
    Option (List CoreStmt) := do
  let returnTys ←
    match
        Expr.externalCallDeclaredReturnTysWithKindEnv?
          storageNames env externalCallKindEnv expr with
    | some tys => some tys
    | none => VarBindings.sourceTysIncludingAnonymous? bindings
  if bindings.length == returnTys.length then
    some ()
  else
    none
  let decls ← VarBindings.toCoreTupleDecls? bindings
  let returnBindings ← Tys.toExternalReturnBindings? "__ext" returnTys
  let assigns ←
    VarBindings.assignFromExternalReturnBindings? bindings returnBindings
  let callCore ←
    Expr.externalCallWithReturnsCoreWithKindEnv?
      (argEnvLower := argEnvLower)
      storageNames env externalCallKindEnv "__ext" returnTys expr
      (fun _ => SolidCore.Solidity.Source.Stmt.block assigns)
  some (decls ++ [callCore])

def storageArrayPushAssignCore? (storageNames : List Name)
    (name : Name) (rhs : Expr) : Option CoreStmt := do
  let name ← stateNameRuntimeKey? name storageNames
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

def storageArrayPushPathAssignCore? (storageNames : List Name)
    (target rhs : Expr) : Option CoreStmt := do
  let (name, indexes) ← Expr.storagePathCore? storageNames target
  match indexes with
  | [] => storageArrayPushAssignCore? storageNames name rhs
  | _ =>
      let rhsCore ← Expr.toCore? storageNames rhs
      some
        (SolidCore.Solidity.Source.Stmt.storageArrayPushPathAssign
          name indexes rhsCore)

/-- PUSH-FIELD-LVALUE: lower an assignment whose LHS writes THROUGH the storage
    reference returned by a zero-arg `.push()`, e.g. `xs.push().a = 7` (after the
    struct-member→index rewrite this is `xs.push()[0] = 7`) or `ys.push()[1] = 9`
    for a fixed-array element. Emits, in solc's order, the push (growing the
    array) followed by an assign to the indexed sub-path of the newly-appended
    last element. The last-element slot is computed exactly as the direct
    push-assign / push-return-alias paths do — via `storageLastPushedIndexExpr`
    over the array's `storagePathCore?` (`storage(name) - 1` after the push).
    Returns `none` for a non-push LHS (the caller then falls back to the ordinary
    lvalue lowering) and for a bare `xs.push() = v` (handled by its own arm) or a
    nested push-target path (unsupported; unchanged over-reject, no regression). -/
def storageArrayPushIndexedAssignCore? (storageNames : List Name)
    (lhs rhs : Expr) : Option CoreStmt := do
  let (target, trailing) ← Expr.stripPushIndexPath? lhs
  match trailing with
  | [] => none
  | _ =>
      let (name, indexes) ← Expr.storagePathCore? storageNames target
      match indexes with
      | [] => do
          let rhsCore ← Expr.toCore? storageNames rhs
          let trailingCore ← mapOption (Expr.toCore? storageNames) trailing
          let lastIndex := storageLastPushedIndexExpr name []
          let baseLv :=
            SolidCore.Solidity.Source.LValue.storageIndex name lastIndex
          let lv :=
            trailingCore.foldl
              (fun acc idx => SolidCore.Solidity.Source.LValue.index acc idx)
              baseLv
          some
            (SolidCore.Solidity.Source.Stmt.block
              [ SolidCore.Solidity.Source.Stmt.storageArrayPush name none
              , SolidCore.Solidity.Source.Stmt.assign lv rhsCore ])
      | _ => none

def storageArrayPushPathCore? (storageNames : List Name)
    (target : Expr) (value? : Option Expr) : Option CoreStmt :=
  match target with
  -- TERNARY-PUSH-TARGET: `(cond ? b : a).push(v)` pushes on the storage array
  -- the ternary SELECTS at runtime — solc evaluates the ternary to a storage
  -- reference lvalue, then pushes. `Expr.storagePathCore?` only names an ident/
  -- index path (returning `none` here would fall the whole contract closed to a
  -- revert), so branch the push into an `ifElse`: `if cond { b.push(v) } else {
  -- a.push(v) }`. Only the taken branch runs, so `v` is evaluated once — the
  -- same on-chain effect as selecting-then-pushing. Recurses so either branch
  -- may itself be a nested ternary or an index path.
  | Expr.ternary cond thenTarget elseTarget => do
      let condCore ← Expr.toCore? storageNames cond
      let thenStmt ← storageArrayPushPathCore? storageNames thenTarget value?
      let elseStmt ← storageArrayPushPathCore? storageNames elseTarget value?
      some (SolidCore.Solidity.Source.Stmt.ifElse condCore thenStmt elseStmt)
  | _ => do
    let (name, indexes) ← Expr.storagePathCore? storageNames target
    let valueCore? ←
      match value? with
      | some value => do
          let valueCore ← Expr.toCore? storageNames value
          some (some valueCore)
      | none => some none
    match indexes with
    | [] =>
        some (SolidCore.Solidity.Source.Stmt.storageArrayPush name valueCore?)
    | _ =>
        some
          (SolidCore.Solidity.Source.Stmt.storageArrayPushPath
            name indexes valueCore?)

def storageReferenceBindingSupported? (binding : VarBinding) : Option Unit := do
  let ty ← binding.ty
  match Ty.toCore? ty with
  | some _ => some ()
  | none =>
      match Ty.toCoreStorageLayout? ty with
      | some _ => some ()
      | none => none

def storagePathValueExpr (name : Name) (indexes : List CoreExpr) : CoreExpr :=
  match indexes with
  | [] => SolidCore.Solidity.Source.Expr.storage name
  | _ => SolidCore.Solidity.Source.Expr.storagePath name indexes

def storageLastPushedIndexExpr (name : Name)
    (indexes : List CoreExpr) : CoreExpr :=
  SolidCore.Solidity.Source.Expr.binary
    SolidCore.Solidity.Source.BinaryOp.sub
    (SolidCore.Solidity.Source.Expr.length
      (storagePathValueExpr name indexes))
    (SolidCore.Solidity.Source.Expr.word 1)

def storageArrayPushReturnAliasCore? (storageNames : List Name)
    (binding : VarBinding) (target : Expr) :
    Option (CoreStmt × CoreStmt) := do
  let localName ← binding.name
  match binding.location with
  | some DataLocation.storage =>
      storageReferenceBindingSupported? binding
      let (name, indexes) ← Expr.storagePathCore? storageNames target
      match indexes with
      | [] =>
          let pushStmt ← storageArrayPushPathCore? storageNames target none
          let lastIndex := storageLastPushedIndexExpr name indexes
          some
            ( pushStmt
            , SolidCore.Solidity.Source.Stmt.storageAliasPath
                localName name [lastIndex] )
      | _ =>
          -- Evaluate an indexed receiver once, push, and bind the returned
          -- reference atomically.  Spelling this as a push followed by an
          -- alias repeated every index expression (e.g. xs[i++].push()), so
          -- the alias pointed into a different outer array.
          some
            ( SolidCore.Solidity.Source.Stmt.storageArrayPushPathAlias
                localName name indexes
            , SolidCore.Solidity.Source.Stmt.skip )
  | _ => none

def storageArrayPushReturnAliasBlockCore? (storageNames : List Name)
    (binding : VarBinding) (target : Expr) : Option CoreStmt := do
  let (pushStmt, aliasStmt) ←
    storageArrayPushReturnAliasCore? storageNames binding target
  some (SolidCore.Solidity.Source.Stmt.block [pushStmt, aliasStmt])

def storageArrayPopPathCore? (storageNames : List Name)
    (target : Expr) : Option CoreStmt := do
  let (name, indexes) ← Expr.storagePathCore? storageNames target
  match indexes with
  | [] => some (SolidCore.Solidity.Source.Stmt.storageArrayPop name)
  | _ =>
      some
        (SolidCore.Solidity.Source.Stmt.storageArrayPopPath name indexes)

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

def Expr.storagePathCore? (storageNames : List Name) :
    Expr -> Option (Name × List CoreExpr)
  | Expr.ident name =>
      match stateNameRuntimeKey? name storageNames with
      | some key => some (key, [])
      | none => none
  | Expr.call (Expr.typeName Ty.bytes) [Arg.positional inner]
  | Expr.call (Expr.typeName Ty.string) [Arg.positional inner] =>
      -- A storage string/bytes conversion is a layout-preserving reference
      -- reinterpretation. Mutation paths such as `bytes(s).push(v)` must keep
      -- pointing at `s`, just like indexed writes already do in `toCoreLValue?`.
      Expr.storagePathCore? storageNames inner
  | Expr.index base index => do
      let (name, indexes) ← Expr.storagePathCore? storageNames base
      let indexCore ← Expr.toCore? storageNames index
      some (name, indexes ++ [indexCore])
  | _ => none

-- Lower ONE `storage`-location tuple-decl binding paired with its RHS component
-- to a direct storage-pointer alias declaration — byte-identically to the
-- single-binding `T storage p = <item>;` lowering (see the `some
-- DataLocation.storage, some source` arm of the varDecl dispatch). solc binds a
-- declared `T storage` local to the RHS component's storage LVALUE (a pointer),
-- so a later write THROUGH the local reaches the pointed-to state variable.
def VarBinding.toStoragePtrTupleDecl? (storageNames : List Name)
    (binding : VarBinding) (item : Expr) : Option CoreStmt := do
  let name ← binding.name
  match item with
  | Expr.call (Expr.member target "push") [] =>
      storageArrayPushReturnAliasBlockCore? storageNames binding target
  | _ => do
      storageReferenceBindingSupported? binding
      let (target, indexes) ← Expr.storagePathCore? storageNames item
      match indexes with
      | [] => some (SolidCore.Solidity.Source.Stmt.storageAlias name target)
      | _ =>
          some
            (SolidCore.Solidity.Source.Stmt.storageAliasPath
              name target indexes)

-- Is every binding of a tuple declaration a named `storage` pointer?
def VarBindings.allStoragePointers : List VarBinding -> Bool
  | [] => true
  | binding :: rest =>
      binding.location == some DataLocation.storage &&
        binding.name.isSome &&
        VarBindings.allStoragePointers rest

-- Is every named binding a `storage` pointer, with declaration holes paired
-- only with effect-free literals (or an explicit source tuple hole)?
def VarBindings.allStoragePointersOrDiscardedLiterals :
    List VarBinding -> List TupleItem -> Bool
  | [], [] => true
  | { name := none, ty := none, location := none } :: bindings,
      TupleItem.value (Expr.literal _) :: items =>
      VarBindings.allStoragePointersOrDiscardedLiterals bindings items
  | { name := none, ty := none, location := none } :: bindings,
      TupleItem.hole :: items =>
      VarBindings.allStoragePointersOrDiscardedLiterals bindings items
  | binding :: bindings, TupleItem.value _ :: items =>
      binding.location == some DataLocation.storage &&
        binding.name.isSome &&
        VarBindings.allStoragePointersOrDiscardedLiterals bindings items
  | _, _ => false

def VarBindings.toStoragePtrTupleDecls? (storageNames : List Name) :
    List VarBinding -> List TupleItem -> Option (List CoreStmt)
  | [], [] => some []
  | { name := none, ty := none, location := none } :: bindings,
      TupleItem.value (Expr.literal _) :: items =>
      VarBindings.toStoragePtrTupleDecls? storageNames bindings items
  | { name := none, ty := none, location := none } :: bindings,
      TupleItem.hole :: items =>
      VarBindings.toStoragePtrTupleDecls? storageNames bindings items
  | binding :: bindings, TupleItem.value item :: items => do
      let head ← VarBinding.toStoragePtrTupleDecl? storageNames binding item
      let tail ← VarBindings.toStoragePtrTupleDecls? storageNames bindings items
      some (head :: tail)
  | _, _ => none
termination_by bindings _ => sizeOf bindings

-- STORAGE-POINTER TUPLE DECLARATION (`(S storage p, S storage q) = (y, x)`): a
-- multi-binding tuple decl EVERY component of which is a `storage`-location
-- pointer. The generic literal-tuple lowering (`tupleVarDeclCorePieces?`)
-- declared each such local with a plain `Stmt.varDecl` (a fresh local holding
-- the aggregate's DEFAULT value) then ran the flat `assignTuple`; its
-- storage-pointer RE-POINT path only fires when the target local ALREADY holds a
-- storage ref, which a freshly default-declared local does not, so the RHS was
-- DEREFERENCED into the local and writes THROUGH it never reached storage (`run`
-- returned 102 with storage unchanged instead of 2112). Instead bind each local
-- directly to its component's storage lvalue, LEFT to RIGHT — identical to the
-- single-binding `T storage p = <item>;` lowering. All components are pure
-- lvalue resolutions (no contents read), so per-item binding matches solc's
-- "evaluate the whole RHS tuple, then bind" order observably. Returns `none`
-- (caller falls back to the generic path) unless every binding is a named
-- storage pointer and every component is a lowerable storage path.
def tupleVarDeclAllStorageCore? (storageNames : List Name)
    (bindings : List VarBinding) (items : List TupleItem) :
    Option (List CoreStmt) := do
  if bindings.length == items.length then some () else none
  if VarBindings.allStoragePointersOrDiscardedLiterals bindings items then
    some ()
  else none
  VarBindings.toStoragePtrTupleDecls? storageNames bindings items

def Expr.storageRefPathCore? (storageRefEnv : StorageRefEnv)
    (storageNames : List Name) :
    Expr -> Option (Name × List CoreExpr)
  | Expr.ident name =>
      if (stateNameRuntimeKey? name storageNames).isSome then
        none
      else if StorageRefEnv.isStorageRef storageRefEnv name then
        some (name, [])
      else
        none
  | Expr.index base index => do
      let (name, indexes) ←
        Expr.storageRefPathCore? storageRefEnv storageNames base
      let indexCore ← Expr.toCore? storageNames index
      some (name, indexes ++ [indexCore])
  | _ => none

def Expr.noReturnEffectStmtCore? (storageNames : List Name) :
    Expr -> Option CoreStmt
  | Expr.unary UnaryOp.delete target => do
      let targetCore ← Expr.toCoreLValue? storageNames target
      some (SolidCore.Solidity.Source.Stmt.deleteValue targetCore)
  | Expr.call (Expr.member target "push") [Arg.positional value] =>
      storageArrayPushPathCore? storageNames target (some value)
  | Expr.call (Expr.member target "pop") [] =>
      storageArrayPopPathCore? storageNames target
  | Expr.call (Expr.member target "transfer") [Arg.positional value] =>
      Expr.transferCore? storageNames target value
  | Expr.call (Expr.ident "selfdestruct") [Arg.positional recipient] => do
      let recipientCore ← Expr.toCore? storageNames recipient
      some (SolidCore.Solidity.Source.Stmt.selfdestruct recipientCore)
  | Expr.call (Expr.ident "assert") [Arg.positional cond] => do
      let condCore ← Expr.toCore? storageNames cond
      some (SolidCore.Solidity.Source.Stmt.assertStmt condCore)
  | Expr.call (Expr.ident "require") [Arg.positional cond] => do
      let condCore ← Expr.toCore? storageNames cond
      some (SolidCore.Solidity.Source.Stmt.requireStmt condCore none)
  | Expr.call (Expr.ident "require")
      [Arg.positional cond, Arg.positional (Expr.literal (Literal.string reason))] => do
      let condCore ← Expr.toCore? storageNames cond
      some (SolidCore.Solidity.Source.Stmt.requireStmt condCore (some reason))
  | Expr.call (Expr.ident "require")
      [Arg.positional cond, Arg.positional (Expr.call (Expr.ident name) args)] => do
      let condCore ← Expr.toCore? storageNames cond
      let coreArgs ← Args.toCoreExprs? storageNames args
      some
        (SolidCore.Solidity.Source.Stmt.requireCustom
          condCore name coreArgs)
  -- REVERT-QUAL (#77), require form in the effect-position lowering (e.g.
  -- `require(a > 0, Base.Err(a))` used as a returned effect): resolve the
  -- base-/self-qualified member-access error callee by its UNQUALIFIED `name`,
  -- mirroring the bare-ident `requireCustom` arm. Must precede the generic
  -- `[cond, reason]` arm. The require-custom checker's member arm also accepts
  -- LIBRARY-qualified errors (`require(cond, L.Bad(a))`); resolving by the bare
  -- `name` is sound because the library qualifier is not part of the selector.
  | Expr.call (Expr.ident "require")
      [Arg.positional cond,
       Arg.positional
         (Expr.call (Expr.member (Expr.typeName (Ty.user _)) name) args)] => do
      let condCore ← Expr.toCore? storageNames cond
      let coreArgs ← Args.toCoreExprs? storageNames args
      some
        (SolidCore.Solidity.Source.Stmt.requireCustom
          condCore name coreArgs)
  | Expr.call (Expr.ident "require")
      [Arg.positional cond, Arg.positional reason] => do
      let condCore ← Expr.toCore? storageNames cond
      let reasonCore ← Expr.toCore? storageNames reason
      some
        (SolidCore.Solidity.Source.Stmt.requireErrorExpr
          condCore reasonCore)
  | Expr.call (Expr.ident "revert") [] =>
      some (SolidCore.Solidity.Source.Stmt.revertError none)
  | Expr.call (Expr.ident "revert")
      [Arg.positional (Expr.literal (Literal.string reason))] =>
      some (SolidCore.Solidity.Source.Stmt.revertError (some reason))
  | Expr.call (Expr.ident "revert") [Arg.positional reason] => do
      let reasonCore ← Expr.toCore? storageNames reason
      some (SolidCore.Solidity.Source.Stmt.revertErrorExpr
        reasonCore)
  | _ => none

def CoreStmt.thenReturnEmpty (stmt : CoreStmt) : CoreStmt :=
  SolidCore.Solidity.Source.Stmt.block
    [ stmt
    , SolidCore.Solidity.Source.Stmt.returnValues [] ]

end

def Expr.abiTyWithEnv? (env : TypeEnv) : Expr -> Option Ty
  | Expr.ident name => TypeEnv.lookup? env name
  | Expr.call
      (Expr.member (Expr.typeName ty@(Ty.user _)) "wrap") [_] =>
      some ty
  | Expr.call
      (Expr.member
        (Expr.member (Expr.typeName (Ty.user parentPath)) typeName) "wrap") [_] =>
      some (Ty.user { segments := parentPath.segments ++ [typeName] })
  | Expr.tuple [] => some (Ty.tuple [])
  | Expr.tuple (TupleItem.hole :: _) => none
  | Expr.tuple (TupleItem.value head :: rest) => do
      -- Infer tuple components recursively instead of requiring an explicit
      -- type wrapper on every item.  Spelling the list recursion through a
      -- smaller tuple keeps the structural decrease visible to Lean.
      let headTy ← Expr.abiTyWithEnv? env head
      let restTy ← Expr.abiTyWithEnv? env (Expr.tuple rest)
      match restTy with
      | Ty.tuple restTys => some (Ty.tuple (headTy :: restTys))
      | _ => none
  | Expr.ternary _ thenExpr elseExpr => do
      -- `Expr.abiTy?` is deliberately env-less and can therefore infer a
      -- conditional from only its first branch when the other branch is an
      -- identifier.  Infer both branches here before consulting that fast
      -- path so mixed-width conditionals retain their common source type.
      let thenTy ← Expr.abiTyWithEnv? env thenExpr
      let elseTy ← Expr.abiTyWithEnv? env elseExpr
      if Expr.isRawNumberLiteralExpression elseExpr &&
          implicitLiteralFits thenTy elseExpr then
        some thenTy
      else if Expr.isRawNumberLiteralExpression thenExpr &&
          implicitLiteralFits elseTy thenExpr then
        some elseTy
      else
        match Ty.commonImplicit? thenTy elseTy with
        | some commonTy => some commonTy
        | none => some thenTy
  | expr =>
      match Expr.abiTy? [] expr with
      | some ty => some ty
      | none =>
          match expr with
          | Expr.unary UnaryOp.bitNot inner =>
              Expr.abiTyWithEnv? env inner
          | Expr.unary UnaryOp.neg inner =>
              Expr.abiTyWithEnv? env inner
          | Expr.unary UnaryOp.preIncrement inner
          | Expr.unary UnaryOp.preDecrement inner
          | Expr.unary UnaryOp.postIncrement inner
          | Expr.unary UnaryOp.postDecrement inner =>
              Expr.abiTyWithEnv? env inner
          | Expr.assign lhs _ _ =>
              Expr.abiTyWithEnv? env lhs
          | Expr.binary op lhs rhs =>
              match op with
              | BinaryOp.lt | BinaryOp.gt | BinaryOp.le | BinaryOp.ge
              | BinaryOp.eq | BinaryOp.ne
              | BinaryOp.boolAnd | BinaryOp.boolOr => some Ty.bool
              -- Solidity shifts and exponentiation keep the left operand's
              -- type.  The other arithmetic and bitwise operators use the
              -- common operand type, including at every level of a
              -- left-associated chain.  Returning only the left leaf here
              -- made `uint16 x; uint56 y; uint8 z; x ^ y ^ z` appear to have
              -- type uint16 and inserted a spurious checked narrowing around
              -- the inner uint56 result.
              | BinaryOp.shl | BinaryOp.shr | BinaryOp.sar | BinaryOp.exp =>
                  Expr.abiTyWithEnv? env lhs
              | _ => do
                  let lhsTy ← Expr.abiTyWithEnv? env lhs
                  let rhsTy ← Expr.abiTyWithEnv? env rhs
                  if Expr.isRawNumberLiteralExpression rhs &&
                      implicitLiteralFits lhsTy rhs then
                    some lhsTy
                  else if Expr.isRawNumberLiteralExpression lhs &&
                      implicitLiteralFits rhsTy lhs then
                    some rhsTy
                  else
                    let lhsTy' :=
                      if Expr.isRawNumberLiteralExpression lhs then
                        (Expr.untypedLiteralMobileTy? lhs).getD lhsTy
                      else lhsTy
                    let rhsTy' :=
                      if Expr.isRawNumberLiteralExpression rhs then
                        (Expr.untypedLiteralMobileTy? rhs).getD rhsTy
                      else rhsTy
                    Ty.commonImplicit? lhsTy' rhsTy'
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
          | Expr.member base "selector" => do
              match Expr.abiTyWithEnv? env base with
              | some (Ty.functionWithLocations _ _ _ _ _ Visibility.external_) =>
                  some (Ty.bytesN 4)
              | _ => none
          | Expr.member base "address" => do
              match Expr.abiTyWithEnv? env base with
              | some (Ty.functionWithLocations _ _ _ _ _ Visibility.external_) =>
                  some (Ty.address false)
              | _ => none
          | Expr.index base indexExpr => do
              let baseTy ← Expr.abiTyWithEnv? env base
              match Ty.fixedBytesSize? baseTy with
              | some _ => some (Ty.bytesN 1)
              | none =>
                  match baseTy with
                  | Ty.bytes => some (Ty.bytesN 1)
                  | Ty.array elementTy _ => some elementTy
                  | Ty.mapping _ valueTy => some valueTy
                  | Ty.tuple elements => do
                      let index ← Expr.numberLiteralNat? indexExpr
                      listGet? elements index
                  | Ty.struct _ elements => do
                      let index ← Expr.numberLiteralNat? indexExpr
                      listGet? elements index
                  | _ => none
          | Expr.slice base _ _ => do
              match Expr.abiTyWithEnv? env base with
              | some Ty.bytes => some Ty.bytes
              | some Ty.string => some Ty.string
              | some (Ty.array elementTy _) =>
                  some (Ty.array elementTy none)
              | _ => none
          | _ => none

def Expr.toCoreAssignOpWithEnv? (storageNames : List Name)
    (env : TypeEnv) : Expr -> Option CoreExpr
  | Expr.assign lhs op rhs => do
      let coreOp ← AssignOp.toCoreBinary? op
      let lhsCore ← Expr.toCoreLValue? storageNames lhs
      let rhsCore ← Expr.toCore? storageNames rhs
      let lhsTy ← Expr.abiTyWithEnv? env lhs
      let cleanup ← Ty.toCoreValueCleanup? lhsTy
      some
        (SolidCore.Solidity.Source.Expr.assignOpCleanupExpr
          lhsCore.toExpr coreOp rhsCore cleanup)
  | _ => none

def Expr.toCoreIncDecWithEnv? (env : TypeEnv)
    (lowerLValue : Expr -> Option CoreLValue) :
    Expr -> Option CoreExpr
  | Expr.unary op target => do
      let (coreOp, returnOld) ←
        match op with
        | UnaryOp.preIncrement =>
            some (SolidCore.Solidity.Source.BinaryOp.add, false)
        | UnaryOp.preDecrement =>
            some (SolidCore.Solidity.Source.BinaryOp.sub, false)
        | UnaryOp.postIncrement =>
            some (SolidCore.Solidity.Source.BinaryOp.add, true)
        | UnaryOp.postDecrement =>
            some (SolidCore.Solidity.Source.BinaryOp.sub, true)
        | _ => none
      let targetCore ← lowerLValue target
      let targetTy ← Expr.abiTyWithEnv? env target
      let cleanup ← Ty.toCoreValueCleanup? targetTy
      some
        (SolidCore.Solidity.Source.Expr.incDecCleanup
          targetCore.toExpr coreOp returnOld cleanup)
  | _ => none

/-- NARROW-BITWISE (F1/F2): a bitwise operation whose result is then WIDENED to a
    larger `uintN`/`intN` must first be cleaned at its OWN (operand) width, then
    widened — solc emits `convert_t_uintM_to_t_uintN(op_at_M)`, where the inner
    `op_at_M` already applied `cleanup_t_uintM`. The model must not collapse this
    to a single wide `uintCleanup`/`intCleanup`, which would skip the
    operand-width truncation (`x << k` widened) or panic (`~x` widened).

    The operand-width clean is exactly the truncating cast `implicitCleanupCore?`
    produces at the source type, so this predicate flags the shapes for which
    that source-width clean is the truncating one:
      * a left shift `<<` (any narrow uint/int operand), and
      * `~` on a narrow *unsigned* operand (`~intN` already lands in range, so it
        keeps the checked path and needs no extra operand-width clean). -/
def CoreExpr.needsOperandWidthBitwiseClean (sourceTy : Ty) : CoreExpr -> Bool
  | SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.shl _ _ => true
  | SolidCore.Solidity.Source.Expr.unary
      SolidCore.Solidity.Source.UnaryOp.bitNot _ =>
      match sourceTy with
      | Ty.uint _ => true
      | _ => false
  | _ => false

def Expr.coreAsFromTy? (targetTy sourceTy : Ty) (coreExpr : CoreExpr) :
    Option CoreExpr :=
  if sourceTy == targetTy then
    Ty.implicitCleanupCore? targetTy coreExpr
  else if
      (targetTy == Ty.bytes || targetTy == Ty.string) &&
        (sourceTy == Ty.bytes || sourceTy == Ty.string) then
    some coreExpr
  else
    match targetTy with
    | Ty.struct _ targetFields => do
        match sourceTy with
        | Ty.tuple sourceFields
        | Ty.struct _ sourceFields =>
            if sourceFields == targetFields then
              Ty.implicitCleanupCore? targetTy coreExpr
            else
              none
        | _ => none
    | Ty.uint bits => do
        let bits := if bits == 0 then 256 else bits
        let _ ← Ty.allowsUintCastSource? bits sourceTy
        -- NARROW-BITWISE (F1/F2): clean a widened `<<`/`~` at its operand width
        -- FIRST (truncating cast), then widen — never collapse to one wide clean.
        let operandCleaned :=
          if CoreExpr.needsOperandWidthBitwiseClean sourceTy coreExpr then
            Ty.implicitCleanupCore sourceTy coreExpr
          else
            coreExpr
        some
          (SolidCore.Solidity.Source.Expr.uintCleanup
            bits operandCleaned)
    | Ty.int bits => do
        let bits := if bits == 0 then 256 else bits
        let _ ← Ty.allowsIntCastSource? bits sourceTy
        let operandCleaned :=
          if CoreExpr.needsOperandWidthBitwiseClean sourceTy coreExpr then
            Ty.implicitCleanupCore sourceTy coreExpr
          else
            coreExpr
        some
          (SolidCore.Solidity.Source.Expr.intCleanup
            bits operandCleaned)
    | Ty.bytesN targetSize
    | Ty.fixedBytes targetSize =>
        match sourceTy with
        | Ty.bytes =>
            some
              (SolidCore.Solidity.Source.Expr.fixedBytesFromBytes
                targetSize coreExpr)
        | _ => do
            let sourceSize ←
              Ty.fixedBytesCastWordSourceSize?
                targetSize sourceTy
            some
              (SolidCore.Solidity.Source.Expr.fixedBytesCast
                targetSize sourceSize coreExpr)
    | Ty.enum _ _ =>
        -- Enum-typed target: the operand is an enum value (an `enumFromUInt`
        -- conversion, already range-checked, or another enum of the same
        -- type), stored as its ordinal word. See `Expr.toCoreAs?`.
        some coreExpr
    | _ =>
        if Ty.canImplicitlyConvert sourceTy targetTy then
          some coreExpr
        else
          none

def Expr.boundExternalFunctionValueCoreAs? (storageNames : List Name)
    (targetTy : Ty) : Expr -> Option CoreExpr
  | Expr.member base member => do
      match targetTy with
      | Ty.functionWithLocations paramTys _ _ _ _ Visibility.external_ => do
          let signature ← externalFunctionSignature? member paramTys
          let baseCore ← Expr.toCore? storageNames base
          some
            (SolidCore.Solidity.Source.Expr.externalFunctionValue
              baseCore
              (SolidCore.Solidity.Source.ABI.selectorFromSignature
                signature))
      | _ => none
  | _ => none

def Expr.toCoreAsWithEnvDirect? (storageNames : List Name) (env : TypeEnv)
    (targetTy : Ty) (expr : Expr) : Option CoreExpr :=
  match Expr.boundExternalFunctionValueCoreAs? storageNames targetTy expr with
  | some coreExpr => some coreExpr
  | none =>
      match Expr.toCoreAs? storageNames targetTy expr with
      | some coreExpr => some coreExpr
      | none =>
          match Expr.toCoreFixedBytesLiteralAs? targetTy expr with
          | some coreExpr => some coreExpr
          | none =>
              if Ty.isFixedBytes targetTy &&
                  Expr.isFixedBytesLiteralCandidate expr then
                none
              else
                match Expr.toCoreNumericLiteralAs? targetTy expr with
                | some coreExpr => some coreExpr
                | none =>
                    if Ty.isIntOrUint targetTy &&
                        Expr.isRawNumberLiteralExpression expr then
                      none
                    else do
                      let sourceTy ← Expr.abiTyWithEnv? env expr
                      let coreExpr ← Expr.toCore? storageNames expr
                      Expr.coreAsFromTy? targetTy sourceTy coreExpr

/-- FB1: a `bytesN`-typed expression whose top node is a shift or bitwise
    operator. These are the shapes whose right-aligned lowering can carry (or
    hide) bits above the low `size`-byte lane, so they are routed through
    `Expr.toCoreFixedBytesBitOp?` for solc-faithful per-op lane cleanup. -/
def Expr.isFixedBytesBitOpShape : Expr -> Bool
  | Expr.call (Expr.typeName (Ty.bytesN _)) [Arg.positional inner]
  | Expr.call (Expr.typeName (Ty.fixedBytes _)) [Arg.positional inner] =>
      Expr.isFixedBytesBitOpShape inner
  | Expr.binary BinaryOp.shl _ _ => true
  | Expr.binary BinaryOp.shr _ _ => true
  | Expr.binary BinaryOp.bitAnd _ _ => true
  | Expr.binary BinaryOp.bitOr _ _ => true
  | Expr.binary BinaryOp.bitXor _ _ => true
  | Expr.unary UnaryOp.bitNot _ => true
  | _ => false

/-- FB1: lower a `bytesN`-typed shift/bitwise subtree, inserting the lane
    cleanup solc emits after every `bytesN <<` and `~bytesN`.

    solc stores `bytesN` **left-aligned** and wraps every `<<` and `~` result in
    `cleanup_t_bytesN`. solidity-lean stores `bytesN` **right-aligned** (meaningful
    bytes low), so `<<` and `~` are exactly the operators that push meaningful
    bits *above* the low `size`-byte lane. Each such result is masked back with
    `fixedBytesCast size size` (take the low `size` bytes — a no-op for
    `size = 32`). `>>`, `&`, `|`, `^` keep in-lane values in-lane and get no
    extra mask, but the subtree is still walked so a nested `<<`/`~` beneath them
    is cleaned (e.g. `(b << 4) >> 4`). Leaves fall back to the ordinary typed
    lowering at `bytesN size`; shift counts (`rhs`) are `uint`, lowered as usual. -/
def Expr.toCoreFixedBytesBitOp? (storageNames : List Name) (env : TypeEnv)
    (size : Nat) : Expr -> Option CoreExpr
  | Expr.call (Expr.typeName (Ty.bytesN castSize)) [Arg.positional inner]
  | Expr.call (Expr.typeName (Ty.fixedBytes castSize)) [Arg.positional inner] =>
      if castSize == size then
        Expr.toCoreFixedBytesBitOp? storageNames env size inner
      else
        Expr.toCoreAsWithEnvDirect?
          storageNames env (Ty.bytesN size)
            (Expr.call (Expr.typeName (Ty.bytesN castSize))
              [Arg.positional inner])
  | Expr.binary BinaryOp.shl lhs rhs => do
      let lhsCore ← Expr.toCoreFixedBytesBitOp? storageNames env size lhs
      let rhsCore ← Expr.toCore? storageNames rhs
      some
        (SolidCore.Solidity.Source.Expr.fixedBytesCast size size
          (SolidCore.Solidity.Source.Expr.binary
            SolidCore.Solidity.Source.BinaryOp.shl lhsCore rhsCore))
  | Expr.binary BinaryOp.shr lhs rhs => do
      let lhsCore ← Expr.toCoreFixedBytesBitOp? storageNames env size lhs
      let rhsCore ← Expr.toCore? storageNames rhs
      some
        (SolidCore.Solidity.Source.Expr.binary
          SolidCore.Solidity.Source.BinaryOp.shr lhsCore rhsCore)
  | Expr.binary BinaryOp.bitAnd lhs rhs => do
      let lhsCore ← Expr.toCoreFixedBytesBitOp? storageNames env size lhs
      let rhsCore ← Expr.toCoreFixedBytesBitOp? storageNames env size rhs
      some
        (SolidCore.Solidity.Source.Expr.binary
          SolidCore.Solidity.Source.BinaryOp.bitAnd lhsCore rhsCore)
  | Expr.binary BinaryOp.bitOr lhs rhs => do
      let lhsCore ← Expr.toCoreFixedBytesBitOp? storageNames env size lhs
      let rhsCore ← Expr.toCoreFixedBytesBitOp? storageNames env size rhs
      some
        (SolidCore.Solidity.Source.Expr.binary
          SolidCore.Solidity.Source.BinaryOp.bitOr lhsCore rhsCore)
  | Expr.binary BinaryOp.bitXor lhs rhs => do
      let lhsCore ← Expr.toCoreFixedBytesBitOp? storageNames env size lhs
      let rhsCore ← Expr.toCoreFixedBytesBitOp? storageNames env size rhs
      some
        (SolidCore.Solidity.Source.Expr.binary
          SolidCore.Solidity.Source.BinaryOp.bitXor lhsCore rhsCore)
  | Expr.unary UnaryOp.bitNot inner => do
      let innerCore ← Expr.toCoreFixedBytesBitOp? storageNames env size inner
      some
        (SolidCore.Solidity.Source.Expr.fixedBytesCast size size
          (SolidCore.Solidity.Source.Expr.unary
            SolidCore.Solidity.Source.UnaryOp.bitNot innerCore))
  | expr => Expr.toCoreAsWithEnvDirect? storageNames env (Ty.bytesN size) expr
termination_by expr => sizeOf expr

/-- FB1: typed lowering to `targetTy` that routes `bytesN` shift/bitwise
    subtrees through `Expr.toCoreFixedBytesBitOp?` (solc-faithful lane cleanup),
    and otherwise behaves exactly like `Expr.toCoreAsWithEnvDirect?`. -/
def Expr.toCoreAsWithEnvBitAware? (storageNames : List Name) (env : TypeEnv)
    (targetTy : Ty) (expr : Expr) : Option CoreExpr :=
  match Ty.fixedBytesSize? targetTy with
  | some size =>
      if Expr.isFixedBytesBitOpShape expr then
        Expr.toCoreFixedBytesBitOp? storageNames env size expr
      else
        Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr
  | none => Expr.toCoreAsWithEnvDirect? storageNames env targetTy expr

/-- Untyped numeric literal expressions adopt the other operand's concrete type
    in a binary operation when their folded value fits.  This includes direct
    and negated literals (`a / -2`) and compound constants
    (`type(int).max == 2**255 - 1`).  Restricting adoption to the first two shapes
    left a fitting compound constant at its unsigned mobile type, so an `int256`
    comparison fell through to the env-free core path and type-mismatched.
    `implicitLiteralFits` still rejects out-of-range and wrong-signed values. -/
def Expr.adoptsOperandLiteralTy : Expr -> Bool
  | expr => Expr.isRawNumberLiteralExpression expr

def Expr.commonOperandTyWithEnv? (env : TypeEnv)
    (lhs rhs : Expr) : Option Ty := do
  let lhsTy ← Expr.abiTyWithEnv? env lhs
  let rhsTy ← Expr.abiTyWithEnv? env rhs
  -- Internal function-pointer comparison (`fp == g` / `fp != g`): one operand is
  -- an internal-function value (a var/storage/ternary-derived
  -- `Value.internalFunction` dispatch id) and the other is a bare function NAME —
  -- which `rewriteInternalFnValueIdents` has turned into a number literal (its
  -- abiTy is `uint`, so `commonImplicit?` would otherwise fail and drop the op to
  -- the word-producing env-less path, leaving `internalFunction == word` →
  -- typeMismatch). Adopt the internal-function type so BOTH operands elaborate to
  -- `Expr.internalFunction` via `toCoreAs?` (a dispatch-id compare, matching
  -- solc 0.8.35 legacy). The typechecker rejects a real number vs a fn pointer,
  -- so a number-literal operand here is always a rewritten fn value.
  if Ty.isInternalFunctionValueTy lhsTy &&
      (Ty.isInternalFunctionValueTy rhsTy ||
        (Expr.numberLiteralInt? rhs).isSome) then
    some lhsTy
  else if Ty.isInternalFunctionValueTy rhsTy &&
      (Expr.numberLiteralInt? lhs).isSome then
    some rhsTy
  else if Expr.adoptsOperandLiteralTy rhs && implicitLiteralFits lhsTy rhs then
    some lhsTy
  else if Expr.adoptsOperandLiteralTy lhs && implicitLiteralFits rhsTy lhs then
    some rhsTy
  else
    -- Mirror `Type::commonType` (`Types.cpp:286`) for a typed operand vs an
    -- untyped number literal that does NOT fit it: the common type is
    -- `commonType(typed, literal->mobileType())`, using the literal's
    -- smallest-fitting `uintN`/`intN` (`RationalNumberType::mobileType`) — NOT
    -- the `uint256` that `abiTy?` reports for a bare literal. This keeps lowering
    -- in lockstep with the typechecker (`commonArrayElementTy?`), so
    -- `uint8 a * 300` casts BOTH operands to `uint16` and the checked mul Panics
    -- on overflow exactly as solc's 16-bit arithmetic does. Gate on
    -- `isRawNumberLiteralExpression` (no `T(x)` leaf) so typed conversions keep
    -- their real type; an out-of-range literal (`> 2^256-1`) falls back to
    -- `abiTy?`'s type.
    let lhsTy' :=
      if Expr.isRawNumberLiteralExpression lhs then
        (Expr.untypedLiteralMobileTy? lhs).getD lhsTy
      else lhsTy
    let rhsTy' :=
      if Expr.isRawNumberLiteralExpression rhs then
        (Expr.untypedLiteralMobileTy? rhs).getD rhsTy
      else rhsTy
    Ty.commonImplicit? lhsTy' rhsTy'

-- R2 (env-lowering unification): `Expr.binaryToCoreWithEnvTyped?` and
-- `Expr.binaryToCoreWithEnv?` are now defined AFTER the fuel-carrying mutual
-- recursion below (they lower operands through the FULL env-aware typed
-- lowering, so nested casts/negations/ternaries inside a binary operand keep
-- their operand-width checked cleanup). See `Expr.binaryToCoreWithEnvTypedFuel?`.
/-- A narrow (`N < 256`) `uintN`/`intN` conversion target, as `(signed, bits)`.
    (Word-width `uint256`/`int256` already check at full width, so they need no
    special handling.) -/
def Ty.narrowIntCastTarget? : Ty -> Option (Bool × Nat)
  | Ty.uint bits => if 0 < bits && bits < 256 then some (false, bits) else none
  | Ty.int bits => if 0 < bits && bits < 256 then some (true, bits) else none
  | _ => none

/-- SIGNED-LITERAL-WIDE-CAST (SOUNDNESS): a WORD-width (256-bit, including the
    bare `uint`/`int` spelling `bits = 0`) `uintN`/`intN` conversion target, as
    its signedness. The complement of `Ty.narrowIntCastTarget?` on the int/uint
    family — used by the wide-cast arm of `Expr.toCoreAsWithEnvFuel?` to route
    a signed-literal-mix argument (`uint256(y + 10)`, `int256 y`) through the
    env-aware typed lowering instead of the env-less fallback (whose untyped
    literal lowers as an unsigned WORD while the signed local evaluates to a
    `Value.int` — the interpreter binary arm then typeMismatches → spurious
    Panic 0x00, where solc+EVM compute the real value). -/
def Ty.wordIntCastTarget? : Ty -> Option Bool
  | Ty.uint bits => if bits == 0 || bits == 256 then some false else none
  | Ty.int bits => if bits == 0 || bits == 256 then some true else none
  | _ => none

/-- Overflow-relevant arithmetic operators — the ones whose checked evaluation
    can Panic 0x11/0x12 at the operand width. -/
def BinaryOp.isOverflowArithmetic : BinaryOp -> Bool
  | BinaryOp.add | BinaryOp.sub | BinaryOp.mul
  | BinaryOp.div | BinaryOp.mod | BinaryOp.exp => true
  | _ => false

/-- Peel whole-expression narrow-int/uint conversions off `expr` to reach an
    arithmetic binary underneath, returning its operator and operands. The
    `annotateAbi` pass re-wraps a conversion argument in a redundant same-type
    conversion (`uint8(a + b)` → `uint8(uint8(a + b))`), so the inner arithmetic
    can sit under one or more narrow casts. Peeling only strips casts that wrap
    the *entire* expression — operand-level casts stay inside `Expr.binary`, so
    an explicitly-widened `uint8(uint256(a) + uint256(b))` is untouched and keeps
    its 256-bit (non-panicking) semantics. -/
def Expr.peelToOverflowArithmetic? :
    Expr -> Option (BinaryOp × Expr × Expr)
  | Expr.binary bop lhs rhs =>
      if BinaryOp.isOverflowArithmetic bop then some (bop, lhs, rhs) else none
  | Expr.call (Expr.typeName castTy) [Arg.positional inner] =>
      match Ty.narrowIntCastTarget? castTy with
      | some _ => Expr.peelToOverflowArithmetic? inner
      | none => none
  | _ => none

/-- NEG-NARROW: peel whole-expression narrow-int casts off `expr` to reach a
    unary `-inner` underneath, returning `inner`. `annotateAbi` re-wraps a
    conversion argument in a redundant same-type cast (`int16(-x)` →
    `int16(int16(-x))`), so the unary negation can sit under one or more narrow
    casts; only casts wrapping the *entire* expression are stripped, exactly like
    `Expr.peelToOverflowArithmetic?`. -/
def Expr.peelToNarrowNeg? : Expr -> Option Expr
  | Expr.unary UnaryOp.neg inner => some inner
  | Expr.call (Expr.typeName castTy) [Arg.positional inner] =>
      match Ty.narrowIntCastTarget? castTy with
      | some _ => Expr.peelToNarrowNeg? inner
      | none => none
  | _ => none

/-- SIGNED-LITERAL-WIDE-CAST: peel whole-expression WORD-width (`uint256`/
    `int256`) int conversions off `expr` to reach an arithmetic binary
    underneath — the wide analogue of `Expr.peelToOverflowArithmetic?`, for the
    redundant same-type wrapper `annotateAbi` puts around a conversion argument
    (`uint256(y + 10)` → `uint256(uint256(y + 10))`). Only WIDE casts are
    stripped: a NARROW inner cast (`uint256(uint8(...))`) truncates and must
    keep its existing (Direct) lowering. -/
def Expr.peelToOverflowArithmeticWide? :
    Expr -> Option (BinaryOp × Expr × Expr)
  | Expr.binary bop lhs rhs =>
      if BinaryOp.isOverflowArithmetic bop then some (bop, lhs, rhs) else none
  | Expr.call (Expr.typeName castTy) [Arg.positional inner] =>
      match Ty.wordIntCastTarget? castTy with
      | some _ => Expr.peelToOverflowArithmeticWide? inner
      | none => none
  | _ => none

/-- NARROW-SHL-MASK (S, narrow-shl-mask-in-abiencode-arg): does `expr` reach a
    left shift `<<` after peeling whole-expression narrow (`uintN`/`intN`,
    N < 256) casts? A `<<` result is typed by solc at the LEFT-operand width and
    cleaned with `cleanup_t_uintN` (a truncating cast, NOT a range check — shifts
    never overflow-panic), so `uint8 (a << b)` with `1 << 8` truncates to 0. The
    env-less `abi.encode` arg path (`Expr.toAbiEncodeArg?` → `Expr.toCore?`)
    DROPS the narrow cast when it cannot env-lessly type the shift operands
    (parameter/local idents have no `Expr.abiTy?` arm), leaving a bare 256-bit
    `shl` (encoding `1 << 8 = 256`) — a wrong-value soundness gap. `annotateAbi`
    wraps such an argument in exactly this redundant narrow cast (`uintN(a << b)`,
    the operand type it recovers WITH the env), so the shift sits under one or
    more narrow casts, mirroring `Expr.peelToOverflowArithmetic?`. A word-width
    (`uint256`) shift needs no mask and is not peeled here. -/
def Expr.peelToNarrowShl? : Expr -> Bool
  | Expr.binary BinaryOp.shl _ _ => true
  | Expr.call (Expr.typeName castTy) [Arg.positional inner] =>
      match Ty.narrowIntCastTarget? castTy with
      | some _ => Expr.peelToNarrowShl? inner
      | none => false
  | _ => false

/-- NARROW-BITNOT-MASK (S, narrow-bitnot-mask-in-abiencode-arg): does `expr`
    reach a bitwise NOT `~inner` after peeling whole-expression narrow
    (`uintN`/`intN`, N < 256) casts? A `~` result is typed by solc at the operand
    width and cleaned with `cleanup_t_uintN` (`and(not(x),2^N-1)`, a TRUNCATING
    cast, NOT a range check — `~` never overflow-panics), so `uint8 (~a)` with
    `a = 1` truncates `not(1) = 0xff…fe` to `0xfe`. The env-less `abi.encode` arg
    path (`Expr.toAbiEncodeArg?` → `Expr.toCore?`) DROPS the narrow cast when it
    cannot env-lessly type the `~` operand (parameter/local idents have no
    `Expr.abiTy?` arm), leaving a bare 256-bit `bitNot` (encoding
    `0xff…fe = 2^256-2`) — a wrong-value soundness gap. `annotateAbi` wraps such
    an argument in exactly this redundant narrow cast (`uintN(~a)`, the operand
    type it recovers WITH the env), so the `~` sits under one or more narrow
    casts, mirroring `Expr.peelToNarrowShl?`. A word-width (`uint256`) `~` needs
    no mask (its cleanup is the identity) and is not peeled here; a `bytesN` `~`
    (annotated with a non-narrow `bytesN(...)` wrapper) is likewise not peeled. -/
def Expr.peelToNarrowBitNot? : Expr -> Bool
  | Expr.unary UnaryOp.bitNot _ => true
  | Expr.call (Expr.typeName castTy) [Arg.positional inner] =>
      match Ty.narrowIntCastTarget? castTy with
      | some _ => Expr.peelToNarrowBitNot? inner
      | none => false
  | _ => false

/-- NARROW-BITAND-MASK (S, narrow-add-under-bitand-in-abiencode-arg): peel
    whole-expression narrow (`uintN`/`intN`, N < 256) casts off `expr` to reach a
    BITWISE `&`/`|`/`^` underneath, returning its operator and operands. A bitwise
    result is typed by solc at the operands' common type, which computes any
    checked arithmetic operand at THAT width BEFORE the mask — so `(a + b) & 255`
    (`uint8 a,b`) Panics 0x11 on `a + b = 300`, never reaching the `& 255`. The
    env-less `abi.encode` arg path (`Expr.toAbiEncodeArg?` → `Expr.toCore?`) runs
    the operand at 256 bits (`300 & 255 = 44`) — a wrong-value/revert-vs-success
    soundness gap. `annotateAbi` wraps such an argument in the redundant narrow
    cast (`uintN((a + b) & 255)`), so the bitwise op sits under one or more narrow
    casts, mirroring `Expr.peelToOverflowArithmetic?`. A word-width bitwise op is
    not peeled (no mask needed). -/
def Expr.peelToNarrowBitwise? : Expr -> Option (BinaryOp × Expr × Expr)
  | Expr.binary bop lhs rhs =>
      match bop with
      | BinaryOp.bitAnd | BinaryOp.bitOr | BinaryOp.bitXor => some (bop, lhs, rhs)
      | _ => none
  | Expr.call (Expr.typeName castTy) [Arg.positional inner] =>
      match Ty.narrowIntCastTarget? castTy with
      | some _ => Expr.peelToNarrowBitwise? inner
      | none => none
  | _ => none

/-- SIGNED-LITERAL-WIDE-CAST: peel whole-expression WORD-width int casts off
    `expr` to reach a unary `-inner` underneath — the wide analogue of
    `Expr.peelToNarrowNeg?`. -/
def Expr.peelToNegWide? : Expr -> Option Expr
  | Expr.unary UnaryOp.neg inner => some inner
  | Expr.call (Expr.typeName castTy) [Arg.positional inner] =>
      match Ty.wordIntCastTarget? castTy with
      | some _ => Expr.peelToNegWide? inner
      | none => none
  | _ => none

/-- SIGNED-LITERAL-WIDE-CAST (SOUNDNESS): does `expr` contain — at any depth
    through binaries, unary operators, and conversion wrappers — a binary one
    of whose operands is a RAW untyped number literal while the OTHER operand
    is SIGNED-typed (`intN`) under `env`? Exactly these mixes break in the
    env-LESS lowering (`Expr.toCore?`): the untyped literal lowers as an
    unsigned `word` while the signed operand evaluates to a `Value.int`, so the
    interpreter's binary arm typeMismatches → spurious Panic 0x00 (adjudicated:
    `uint256(y + 10)` with `int256 y = 3` Panicked where solc+EVM return 13;
    `-(y * 2)` / `-(y - z * 2)` likewise). Used as the reroute flag by the
    wide-cast and wide-negation arms of `Expr.toCoreAsWithEnvFuel?`: every
    UNFLAGGED expression keeps the byte-identical Direct/env-less path
    (`uint256(y + z)` two typed operands, `-(y - z)` without a literal,
    unsigned `uint256(u + 10)` — the literal and the `uint` local both lower
    as words). -/
def Expr.hasSignedLiteralOperandMix (env : TypeEnv) : Expr -> Bool
  | Expr.binary _ lhs rhs =>
      (Expr.isRawNumberLiteralExpression lhs &&
        !Expr.isRawNumberLiteralExpression rhs &&
        (match Expr.abiTyWithEnv? env rhs with
          | some (Ty.int _) => true
          | _ => false)) ||
      (Expr.isRawNumberLiteralExpression rhs &&
        !Expr.isRawNumberLiteralExpression lhs &&
        (match Expr.abiTyWithEnv? env lhs with
          | some (Ty.int _) => true
          | _ => false)) ||
      Expr.hasSignedLiteralOperandMix env lhs ||
      Expr.hasSignedLiteralOperandMix env rhs
  | Expr.unary _ inner => Expr.hasSignedLiteralOperandMix env inner
  | Expr.call (Expr.typeName _) [Arg.positional inner] =>
      Expr.hasSignedLiteralOperandMix env inner
  | _ => false

/-- NARROW-ADD-WIDE-CAST (SOUNDNESS): does `expr` (the argument of a WORD-width
    `uint256`/`int256` explicit cast) peel — through nested wide casts — to an
    overflow-relevant arithmetic binary whose operand COMMON type is NARROW
    (`uintN`/`intN`, `N < 256`)? `uint256(a + b)` with `uint8 a,b` must evaluate
    `a + b` at its uint8 operand width so the checked-add Panic 0x11 fires BEFORE
    the widening conversion — exactly the narrow-cast H2 obligation, only under a
    WIDE cast. Used (alongside `hasSignedLiteralOperandMix`) as the reroute gate
    of the wide-cast arm of `Expr.toCoreAsWithEnvFuel?`; both flags feed the SAME
    `peelToOverflowArithmeticWide?` → `binaryToCoreWithEnvTypedFuel?` →
    operand-width `implicitCleanupCore` machinery. Explicitly-widened operands
    (`uint256(a) + uint256(b)`) have a WORD operand common type, so this is
    `false` and they keep the byte-identical Direct path. -/
def Expr.wideCastNarrowOverflowArithmetic? (env : TypeEnv) (expr : Expr) : Bool :=
  -- Peel BOTH wide (`uint256(a + b)`, unwrapped) and narrow int-cast wrappers.
  -- The `annotateAbi` pass wraps a conversion argument at the ARGUMENT'S own
  -- type, so `uint256(a + b)` (`uint8 a,b`) reaches this arm as
  -- `uint256(uint8(a + b))` — the WIDE peeler (`peelToOverflowArithmeticWide?`,
  -- word casts only) cannot see the narrow `uint8` wrapper, so also try the
  -- narrow peeler (`peelToOverflowArithmetic?`, narrow casts). Either way, fire
  -- only when the underlying arithmetic's operand COMMON type is narrow.
  let peeled :=
    match Expr.peelToOverflowArithmeticWide? expr with
    | some r => some r
    | none => Expr.peelToOverflowArithmetic? expr
  match peeled with
  | some (_, lhs, rhs) =>
      (match Expr.commonOperandTyWithEnv? env lhs rhs with
       | some ty => (Ty.narrowIntCastTarget? ty).isSome
       | none => false)
  | none => false

/-- NARROW-SHL-WIDE-CAST (SOUNDNESS): does `expr` (the argument of a WORD-width
    `uint256`/`int256` explicit cast) reach — through nested narrow/wide casts —
    a left shift `<<` whose OWN (left-operand) type is NARROW (`uintN`/`intN`,
    `N < 256`)? `uint256(x << 8)` with `uint32 x` must evaluate the shift at its
    uint32 operand width so the bits pushed past bit 31 are TRUNCATED (solc
    cleans a shift result with `cleanup_t_uintN`, a truncating cast — shifts
    never overflow-panic) BEFORE the widening conversion. The env-less Direct
    fallback shifts at 256 bits and never masks (`0xFFFFFFFF << 8 = 0xFFFFFFFF00`
    instead of the truncated `0xFFFFFF00`) — a wrong-value soundness gap. Used
    (alongside `hasSignedLiteralOperandMix` and `wideCastNarrowOverflowArithmetic?`)
    as the reroute gate of the wide-cast arm of `Expr.toCoreAsWithEnvFuel?`; a
    flagged argument routes through the nested-cast fallback, which lowers it at
    ITS OWN type via the env-aware recursion (whose Direct fallback fires the
    truncating operand-width cleanup on the shift). An explicitly-widened operand
    (`uint256(a) << b`) has a WORD shift type, so this is `false` and it keeps the
    byte-identical Direct path (no mask needed). `annotateAbi` may wrap the shift
    in the redundant narrow cast (`uint32(x << 8)`), which `peelToNarrowShl?`
    strips; either spelling reaches the same narrow shift type here. -/
def Expr.wideCastNarrowShl? (env : TypeEnv) (expr : Expr) : Bool :=
  Expr.peelToNarrowShl? expr &&
    (match Expr.abiTyWithEnv? env expr with
     | some ty => (Ty.narrowIntCastTarget? ty).isSome
     | none => false)

/-- TC1: lower an `abi.encode`/`abi.encodePacked` CONDITIONAL argument whose two
    branches are `bytesN` of DIFFERENT widths. The conditional takes the
    ternary's COMMON type (the wider `bytesN`); solc inserts the implicit
    `convert_t_bytesM_to_t_bytesN` on the narrower branch, and because `bytesN`
    is left-aligned that widening moves the content into the HIGH bytes
    (`bytes2 0xaabb` -> `bytes4 0xaabb0000`). The env-less abi argument path
    lowers each branch with NO target type, so no cast is inserted and the
    narrow branch keeps its low-byte (right-aligned) content -> wrong alignment.
    Here each branch is lowered to the recomputed common type via the typed env
    path (which inserts the `fixedBytesCast`), mirroring the already-correct
    return/assignment ternary lowering at `Expr.toCoreAsWithEnv?`. -/
def Expr.abiEncodeFixedBytesTernaryCore? (storageNames : List Name) (env : TypeEnv)
    (cond thenExpr elseExpr : Expr) : Option (Ty × CoreExpr) := do
  let thenTy ← Expr.abiTyWithEnv? env thenExpr
  let elseTy ← Expr.abiTyWithEnv? env elseExpr
  let commonTy := (Ty.commonImplicit? thenTy elseTy).getD thenTy
  -- Only the alignment-carrying `bytesN`/`fixedBytes` common type diverges;
  -- integer branches are stored full-width so widening is a value no-op and
  -- they keep the exact env-less path.
  let _ ← Ty.fixedBytesSize? commonTy
  let condCore ← Expr.toCoreAsWithEnvDirect? storageNames env Ty.bool cond
  let thenCore ← Expr.toCoreAsWithEnvBitAware? storageNames env commonTy thenExpr
  let elseCore ← Expr.toCoreAsWithEnvBitAware? storageNames env commonTy elseExpr
  some
    (commonTy,
      SolidCore.Solidity.Source.Expr.ternary condCore thenCore elseCore)

/-- Detect a `bytesN`-common-type conditional `abi.encode` argument, seeing
    through the redundant `bytesN(...)` wrapper that `annotateAbi` puts around a
    conditional whose branch idents have no standalone `abiTy?`. Returns the
    common type together with the correctly-widened conditional core. -/
def Expr.abiEncodeFixedBytesTernary? (storageNames : List Name) (env : TypeEnv) :
    Expr -> Option (Ty × CoreExpr)
  | Expr.call (Expr.typeName _)
      [Arg.positional (Expr.ternary cond thenExpr elseExpr)] =>
      Expr.abiEncodeFixedBytesTernaryCore? storageNames env cond thenExpr elseExpr
  | Expr.ternary cond thenExpr elseExpr =>
      Expr.abiEncodeFixedBytesTernaryCore? storageNames env cond thenExpr elseExpr
  | _ => none

def Args.anyAbiEncodeFixedBytesTernary? (storageNames : List Name)
    (env : TypeEnv) : List Arg -> Bool
  | [] => false
  | Arg.positional expr :: rest =>
      (Expr.abiEncodeFixedBytesTernary? storageNames env expr).isSome ||
        Args.anyAbiEncodeFixedBytesTernary? storageNames env rest
  | Arg.named _ _ :: rest =>
      Args.anyAbiEncodeFixedBytesTernary? storageNames env rest

/-- Env-carrying `abi.encode` argument lowering: identical to the env-less
    `Args.toAbiEncode?` for every argument EXCEPT a `bytesN`-common-type
    conditional, which is widened per-branch (TC1). -/
def Args.toAbiEncodeWithEnv? (storageNames : List Name) (env : TypeEnv) :
    List Arg -> Option (List CoreTy × List CoreExpr)
  | [] => some ([], [])
  | Arg.positional expr :: rest => do
      let (coreTy, coreExpr) ←
        match Expr.abiEncodeFixedBytesTernary? storageNames env expr with
        | some (ty, core) => do
            let coreTy ← Ty.toCore? ty
            some (coreTy, core)
        | none => Expr.toAbiEncodeArg? storageNames expr
      let (tys, coreExprs) ← Args.toAbiEncodeWithEnv? storageNames env rest
      some (coreTy :: tys, coreExpr :: coreExprs)
  | Arg.named _ _ :: _ => none

/-- Env-carrying `abi.encodePacked` argument lowering (keeps the source types so
    `Tys.packedTopWidths` still computes the packed widths); identical to the
    env-less `Args.toAbiEncodeSource?` except for the `bytesN` conditional (TC1). -/
def Args.toAbiEncodeSourceWithEnv? (storageNames : List Name) (env : TypeEnv) :
    List Arg -> Option (List Ty × List CoreTy × List CoreExpr)
  | [] => some ([], [], [])
  | Arg.positional expr :: rest => do
      let (sourceTy, coreTy, coreExpr) ←
        match Expr.abiEncodeFixedBytesTernary? storageNames env expr with
        | some (ty, core) => do
            let coreTy ← Ty.toCore? ty
            some (ty, coreTy, core)
        | none => Expr.toAbiEncodeSourceArg? storageNames expr
      let (sourceTys, coreTys, coreExprs) ←
        Args.toAbiEncodeSourceWithEnv? storageNames env rest
      some (sourceTy :: sourceTys, coreTy :: coreTys, coreExpr :: coreExprs)
  | Arg.named _ _ :: _ => none

/-- STAGE-D #193: does an `abi.encode*` / `keccak256` / `concat` ARGUMENT carry
    narrow (`uintN`/`intN`, N < 256) CHECKED arithmetic (or a narrow negation, or
    a `uintN`/`intN`/`bytesN` cast wrapping one) that must be evaluated at the
    OPERAND width so its Panic 0x11 fires? The env-less argument path
    (`Expr.toAbiEncodeArg?`) runs such operands at 256 bits, silently wrapping
    (`abi.encode(a + b)` with `uint8 a=200,b=100` hashed/encoded 44/300 instead
    of Panicking). Only these shapes get re-routed through the env-aware
    recursion; every other argument keeps the byte-identical env-less lowering,
    so non-arithmetic args (addresses, hashes, state reads, literals) are
    untouched across every existing lane. `peelToOverflowArithmetic?` /
    `peelToNarrowNeg?` already see through the redundant narrow-int cast wrappers
    `annotateAbi` inserts; the extra `bytesN(...)` clause covers `bytes1(a + b)`
    (a `bytesN` cast the int-only peelers stop at). -/
def Expr.abiArgNeedsEnvCleanupFuel? : Nat -> Expr -> Bool
  | 0, _ => false
  | Nat.succ fuel, expr =>
      match Expr.peelToOverflowArithmetic? expr with
      | some _ => true
      | none =>
      -- ARITH/BUILTIN-UNDER-INT-CAST (S, narrow-addmod-through-cast-arg): an
      -- explicit int cast (WORD `uint256`/`int256` OR NARROW `uintN`/`intN`) is
      -- TRANSPARENT to the operand-width cleanup obligation of what it wraps — the
      -- arg shape `addmod(uint256(a + b), 1, 7)` (`uint128 a,b`) and its cast-
      -- tower variants (`uint128(uint128(addmod(uint256(a + b), 1, 7)))`, the
      -- shape a returned-through-a-fn-pointer arg takes; `annotateAbi` also wraps
      -- the inner `a + b` as `uint256(uint128(a + b))`). solc evaluates `a + b` at
      -- its NARROW operand width (checked add, Panic 0x11 on overflow) BEFORE any
      -- widening/narrowing; the env-less builtin-arg path ran it bare at 256 bits
      -- (no overflow) so the addmod silently returned `(a+b+1) mod m`. The peelers
      -- above stop at a WORD cast, and neither peels a whole builtin call, so
      -- recurse THROUGH the cast to reach the flagged content underneath (the
      -- inner arithmetic or builtin then matches its own arm). Flagging reroutes
      -- the containing position (addmod/mulmod, abi.encode, index key, cast-of-
      -- builtin, …) through the env-aware lowering, whose cast arms (#31 / the
      -- cast-of-builtin arm) fire the operand-width cleanup — the same machinery
      -- the return/vardecl position already uses. A cast over non-flagged content
      -- recurses to `false` (`uint256(x)`, `uint128(y)`) and stays byte-identical.
      match (match expr with
             | Expr.call (Expr.typeName castTy) [Arg.positional inner] =>
                 if (Ty.wordIntCastTarget? castTy).isSome ||
                     (Ty.narrowIntCastTarget? castTy).isSome ||
                     castTy == Ty.bytes || castTy == Ty.string ||
                     (match castTy with | Ty.address _ => true | _ => false) then
                   some inner
                 else none
             | _ => none) with
      | some inner => Expr.abiArgNeedsEnvCleanupFuel? fuel inner
      | none =>
          match Expr.peelToNarrowNeg? expr with
          | some _ => true
          | none =>
          -- NARROW-SHL-MASK (S): a narrow `<<` (possibly under the redundant
          -- narrow cast `annotateAbi` inserts) must lower env-aware so its
          -- operand-width truncating clean fires (`1 << 8 → 0`, not 256).
          if Expr.peelToNarrowShl? expr then true
          -- NARROW-BITNOT-MASK (S): a narrow `~` (possibly under the redundant
          -- narrow cast `annotateAbi` inserts) must lower env-aware so its
          -- operand-width truncating clean fires (`~uint8 1 → 0xfe`, not
          -- `0xff…fe`). `~` is a truncating cleanup, never a range check.
          else if Expr.peelToNarrowBitNot? expr then true
          -- NARROW-BITAND-MASK (S): a bitwise `&`/`|`/`^` (possibly under the
          -- redundant narrow cast `annotateAbi` inserts) whose OWN operand
          -- carries narrow checked arithmetic — `abi.encode((a + b) & 255)`
          -- (`uint8 a,b`). solc computes `a + b` at the operand width BEFORE the
          -- mask, so `a + b == 300` Panics 0x11; the env-less arg path runs it at
          -- 256 bits (`300 & 255 = 44`). Reroute env-aware so the operand-width
          -- cleanup fires. Only when an operand itself needs it — a bitwise op
          -- with no narrow arithmetic stays byte-identical.
          else if (match Expr.peelToNarrowBitwise? expr with
              | some (_, lhs, rhs) =>
                  Expr.abiArgNeedsEnvCleanupFuel? fuel lhs ||
                    Expr.abiArgNeedsEnvCleanupFuel? fuel rhs
              | none => false) then true
          else
              match expr with
              | Expr.call (Expr.typeName castTy) [Arg.positional inner] =>
                  Ty.isFixedBytes castTy &&
                    Expr.abiArgNeedsEnvCleanupFuel? fuel inner
              -- A resolved struct constructor is a tuple of per-field casts.
              -- Look through each cast so a field such as
              -- `bool(a + b > 5)` retains the uintN operand-width check when
              -- the whole struct is consumed by an ABI/builtin boundary.
              | Expr.tuple items =>
                  items.any (fun item =>
                    match item with
                    | TupleItem.value
                        (Expr.call (Expr.typeName _) [Arg.positional inner]) =>
                        Expr.abiArgNeedsEnvCleanupFuel? fuel inner
                    | TupleItem.value e =>
                        Expr.abiArgNeedsEnvCleanupFuel? fuel e
                    | TupleItem.hole => false)
              -- ITEM-1: an inline array literal whose common element type the
              -- env-LESS typer cannot compute (`abiTy?` has no identifier
              -- arm: storage `bytes`/`string`/array state variables,
              -- storage-pointer locals, ternaries over them). Such an
              -- argument was previously an OVER-REJECT (the env-less
              -- lowering fails), so flagging it reroutes only previously
              -- fail-closed statements into the env-aware path, where the
              -- array-literal decline-fallback
              -- (`Expr.abiArrayLiteralWithEnvFuel?`) types and lowers it.
              | Expr.array elems =>
                  (Expr.arrayLiteralCommonTy? [] elems).isNone ||
                    elems.any (Expr.abiArgNeedsEnvCleanupFuel? fuel)
              -- ENCODECALL-ARG (S, narrow-add-abi-encodecall-arg): an argument
              -- that is ITSELF `abi.encodeCall(fnPtr, (…))` whose argument
              -- TUPLE carries narrow checked arithmetic
              -- (`abi.encode(abi.encodeCall(this.g, (a + b)))`, `uint8 a,b`).
              -- solc evaluates each tuple item at the callee-parameter width
              -- (`a + b` at uint8, Panic 0x11 on overflow) while assembling the
              -- encodeCall calldata; the env-aware encodeCall arm of
              -- `Expr.toCoreAsWithEnvFuel?` lowers each item at its own width
              -- via `TupleItems.toAbiEncodeSourceWithEnvFuel?`, so flag when a
              -- tuple item needs the cleanup. Placed BEFORE the generic `abi.*`
              -- arm because encodeCall's second argument is a tuple (not a flat
              -- positional list) so the generic `args.any` cannot reach it.
              | Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
                  [Arg.positional _, Arg.positional (Expr.tuple items)] =>
                  items.any (fun it =>
                    match it with
                    | TupleItem.value e =>
                        Expr.abiArgNeedsEnvCleanupFuel? fuel e
                    | TupleItem.hole => false)
              -- The importer unwraps parenthesized singleton arguments.
              | Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
                  [Arg.positional _, Arg.positional argumentExpr] =>
                  Expr.abiArgNeedsEnvCleanupFuel? fuel argumentExpr
              -- #201 (F): an argument that is ITSELF an `abi.encode*`/`concat`/
              -- hash builtin call needs the env-aware lowering when one of ITS
              -- OWN arguments does (`abi.encode(abi.encodePacked(a + b))`,
              -- `bytes.concat(abi.encode(a + b))`,
              -- `keccak256(bytes.concat(abi.encode(a + b)))`). The env-aware
              -- `abi.*`/hash/concat arms of `Expr.toCoreAsWithEnvFuel?` already
              -- recurse through such an argument; only this FLAG stopped at one
              -- level, so the nested shapes silently fell back env-less.
              | Expr.call (Expr.member (Expr.ident "abi") m) args =>
                  if m == "decode" then
                    match args with
                    | [Arg.positional data, Arg.positional _] =>
                        Expr.abiArgNeedsEnvCleanupFuel? fuel data
                    | _ => false
                  else
                    (m == "encode" || m == "encodePacked" ||
                        m == "encodeWithSelector" ||
                        m == "encodeWithSignature") &&
                      args.any (fun a =>
                        match a with
                        | Arg.positional e =>
                            Expr.abiArgNeedsEnvCleanupFuel? fuel e
                        | Arg.named _ _ => false)
              | Expr.call (Expr.member (Expr.ident "bytes") "concat") args
              | Expr.call (Expr.member (Expr.typeName Ty.bytes) "concat") args
              | Expr.call (Expr.member (Expr.ident "string") "concat") args
              | Expr.call (Expr.member (Expr.typeName Ty.string) "concat") args =>
                  args.any (fun a =>
                    match a with
                    | Arg.positional e =>
                        Expr.abiArgNeedsEnvCleanupFuel? fuel e
                    | Arg.named _ _ => false)
              | Expr.call (Expr.ident hname) [Arg.positional inner] =>
                  (hname == "keccak256" || hname == "sha256" ||
                      hname == "ripemd160") &&
                    Expr.abiArgNeedsEnvCleanupFuel? fuel inner
              -- Value-use boundaries whose direct lowering recursively drops
              -- the type environment.  Flagging them lets the matching
              -- env-aware expression/statement arms retain a nested narrow
              -- arithmetic check before the boundary consumes the value.
              | Expr.call (Expr.ident "ecrecover") args =>
                  args.any (fun a =>
                    match a with
                    | Arg.positional e =>
                        Expr.abiArgNeedsEnvCleanupFuel? fuel e
                    | Arg.named _ _ => false)
              | Expr.member base member =>
                  (member == "balance" || member == "code" ||
                      member == "codehash" || member == "length") &&
                    Expr.abiArgNeedsEnvCleanupFuel? fuel base
              | Expr.payableConversion inner =>
                  Expr.abiArgNeedsEnvCleanupFuel? fuel inner
              -- WS1 (H, addmod/mulmod + new-with-size): these builtins'
              -- evaluate flagged arguments at their own width first (see the
              -- matching env-aware arms), so an argument that IS such a call
              -- with a flagged argument must itself lower env-aware.
              | Expr.call (Expr.ident amName)
                  [Arg.positional amX, Arg.positional amY, Arg.positional amM] =>
                  (amName == "addmod" || amName == "mulmod") &&
                    (Expr.abiArgNeedsEnvCleanupFuel? fuel amX ||
                      Expr.abiArgNeedsEnvCleanupFuel? fuel amY ||
                      Expr.abiArgNeedsEnvCleanupFuel? fuel amM)
              | Expr.newExpr _ [Arg.positional lengthExpr] =>
                  Expr.abiArgNeedsEnvCleanupFuel? fuel lengthExpr
              -- WS1 (H, index subtrees): an argument that is an INDEX read
              -- whose base or key needs the cleanup (`arr[a + b]`,
              -- `arr[arr[a + b]]`, `uint8 a,b`) — the narrow checked
              -- arithmetic evaluates (Panic 0x11) while computing the lookup,
              -- so the whole index expression must lower env-aware. The
              -- env-aware `Expr.index` arm reroutes flagged keys of ANY width
              -- (see the index arm), reaching nested narrow keys inside wide
              -- keys.
              | Expr.index base key =>
                  Expr.abiArgNeedsEnvCleanupFuel? fuel base ||
                    Expr.abiArgNeedsEnvCleanupFuel? fuel key
              -- WS1 (H, calldata-slice bounds): a slice whose bound carries
              -- narrow checked arithmetic (`msg.data[a + b:]`, `uint8 a,b`)
              -- must lower env-aware so the bound Panics 0x11 at its own width
              -- (see the env-aware `Expr.slice` arm).
              | Expr.slice _ start stop =>
                  start.any (Expr.abiArgNeedsEnvCleanupFuel? fuel) ||
                    stop.any (Expr.abiArgNeedsEnvCleanupFuel? fuel)
              -- CONDITIONAL: a flagged subtree in either selected arm, or in
              -- the condition itself, still evaluates before the surrounding
              -- ABI/builtin argument is consumed.  Recurse through the whole
              -- conditional so `abi.encode(c ? a + b : a)` and
              -- `addmod((a + b > n) ? x : y, ...)` retain the uintN/intN
              -- operand-width Panic 0x11.
              | Expr.ternary cond thenExpr elseExpr =>
                  Expr.abiArgNeedsEnvCleanupFuel? fuel cond ||
                    Expr.abiArgNeedsEnvCleanupFuel? fuel thenExpr ||
                    Expr.abiArgNeedsEnvCleanupFuel? fuel elseExpr
              -- An assignment expression produces the assigned value, but its
              -- RHS still evaluates at the LValue's type before an enclosing
              -- ABI/builtin consumer sees it (`abi.encode(s = a + b)`).
              | Expr.assign _ AssignOp.assign rhs =>
                  Expr.abiArgNeedsEnvCleanupFuel? fuel rhs
              -- A compound assignment and an increment/decrement evaluate and
              -- clean up at the LValue's own type before yielding their value.
              -- Mark them directly so an enclosing explicit cast (including
              -- annotateAbi's redundant narrow-cast layer) re-enters the
              -- env-aware assignment/inc-dec lowerers instead of widening the
              -- mutation first.
              | Expr.assign _ _ _ => true
              | Expr.unary UnaryOp.preIncrement _
              | Expr.unary UnaryOp.preDecrement _
              | Expr.unary UnaryOp.postIncrement _
              | Expr.unary UnaryOp.postDecrement _ => true
              | Expr.enumFromUInt _ inner =>
                  Expr.abiArgNeedsEnvCleanupFuel? fuel inner
              -- COMPARISON / BOOLEAN-COMBINATOR (S, narrow-add-comparison-in-
              -- abiencode-arg): a bool-producing operand of `abi.encode*` whose
              -- OWN operand carries narrow checked arithmetic — `abi.encode(a +
              -- b > 5)`, `abi.encode((a + b) < n && …)` (`uint8 a,b`). solc
              -- evaluates `a + b` at uint8 while computing the comparison, so
              -- `a + b == 300` Panics 0x11 BEFORE the comparison yields a bool;
              -- the env-less arg path (`Expr.toAbiEncodeArg?`) runs the operand
              -- at 256 bits (`300 > 5 = true`) and silently returns
              -- `abi.encode(true)`. Reroute so the env-aware comparison /
              -- `&&`/`||` arms (which lower each operand at its own width via
              -- `binaryToCoreWithEnvTypedFuel?`) fire the operand-width cleanup.
              -- Only fires when an operand ITSELF needs the cleanup, so a
              -- comparison with no narrow arithmetic stays byte-identical.
              | Expr.binary op lhs rhs =>
                  match op with
                  -- A shift keeps the left operand's Solidity type. Checked
                  -- arithmetic nested below either shift must therefore run at
                  -- that width before the shift consumes it; a nested `<<`
                  -- also retains its own truncating cleanup under an outer
                  -- `>>`.
                  | BinaryOp.shl | BinaryOp.shr =>
                      Expr.abiArgNeedsEnvCleanupFuel? fuel lhs ||
                        Expr.abiArgNeedsEnvCleanupFuel? fuel rhs
                  | BinaryOp.lt | BinaryOp.gt | BinaryOp.le | BinaryOp.ge
                  | BinaryOp.eq | BinaryOp.ne
                  | BinaryOp.boolAnd | BinaryOp.boolOr =>
                      Expr.abiArgNeedsEnvCleanupFuel? fuel lhs ||
                        Expr.abiArgNeedsEnvCleanupFuel? fuel rhs
                  | _ => false
              -- `!c` in a bool position: the env-aware `logicalNot` arm recurses
              -- on the operand at `Ty.bool`, so a comparison under `!`
              -- (`abi.encode(!((a + b) < n))`) keeps the operand-width cleanup.
              | Expr.unary UnaryOp.logicalNot inner =>
                  Expr.abiArgNeedsEnvCleanupFuel? fuel inner
              | _ => false

/-- #201: nesting budget for the flag above. Keep this aligned with the general
    env-aware lowering budget: valid generated Solidity can easily exceed the
    former depth of eight, and returning `false` at that boundary silently
    removed required narrow arithmetic checks. -/
def defaultAbiCleanupDetectionFuel : Nat := 1024

def Expr.abiArgNeedsEnvCleanup? (expr : Expr) : Bool :=
  Expr.abiArgNeedsEnvCleanupFuel? defaultAbiCleanupDetectionFuel expr

def TupleItems.anyAbiArgNeedsEnvCleanup (items : List TupleItem) : Bool :=
  items.any (fun item =>
    match item with
    | TupleItem.value expr => Expr.abiArgNeedsEnvCleanup? expr
    | TupleItem.hole => false)

/-- STAGE-D #193 (statement side): does a RETURN-position `abi.encode*` /
    `keccak256`/`sha256`/`ripemd160` / `bytes.concat`/`string.concat` call carry
    an argument that needs the env-aware operand-width cleanup
    (`Expr.abiArgNeedsEnvCleanup?`)? The return-statement dispatcher's abi/hash/
    concat arms all bottom out in the env-LESS `Stmt.toCore?`, so the env-aware
    `Expr.toCoreAsWithEnvFuel?` arms (which fire the Panic 0x11) are DEAD for
    `return keccak256(abi.encodePacked(a + b))` etc. unless the dispatcher is
    told to reroute. Only these exact builtin heads are inspected (one nesting
    level for the hash functions, whose single `bytes` argument is itself an
    `abi.encode*`/`concat` call); every other return keeps its lowering
    byte-identical. -/
def Expr.abiBuiltinArgsNeedEnvCleanup : Expr -> Bool
  -- `abi.decode(abi.encode(a + b), (int8))` must evaluate the encoder's
  -- checked addition before decode. The outer decode used to bypass the
  -- var-declaration env-aware route, folding typed casts to an unchecked
  -- constant; decode then rejected the out-of-range value with an empty
  -- revert instead of the addition's Panic(0x11).
  | Expr.call (Expr.member (Expr.ident "abi") "decode")
      [Arg.positional data, Arg.positional _] =>
      Expr.abiBuiltinArgsNeedEnvCleanup data
  -- ENCODECALL-ARG (S, narrow-add-abi-encodecall-arg): a RETURN/vardecl-position
  -- `abi.encodeCall(fnPtr, (…))` whose argument TUPLE carries narrow checked
  -- arithmetic (`return abi.encodeCall(this.g, (a + b))`, `uint8 a,b`). solc
  -- evaluates each tuple item at the callee-parameter width while assembling the
  -- calldata, so `a + b == 300` Panics 0x11 BEFORE the encode completes; without
  -- this reroute the return dispatcher lowered env-less (encoding 300 at 256
  -- bits, silent success). The env-aware encodeCall arm lowers each item at its
  -- own width. Matched before the generic `abi.*` arm since the second argument
  -- is a tuple, not a flat positional list.
  | Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
      [Arg.positional _, Arg.positional (Expr.tuple items)] =>
      items.any (fun it =>
        match it with
        | TupleItem.value e => Expr.abiArgNeedsEnvCleanup? e
        | TupleItem.hole => false)
  | Expr.call (Expr.member (Expr.ident "abi") "encodeCall")
      [Arg.positional _, Arg.positional argumentExpr] =>
      Expr.abiArgNeedsEnvCleanup? argumentExpr
  | Expr.call (Expr.member (Expr.ident "abi") m) args =>
      (m == "encode" || m == "encodePacked" || m == "encodeWithSelector" ||
          m == "encodeWithSignature") &&
        args.any (fun a =>
          match a with
          | Arg.positional e =>
              Expr.abiArgNeedsEnvCleanup? e || Expr.isFixedBytesBitOpShape e
          | Arg.named _ _ => false)
  | Expr.call (Expr.member (Expr.ident "bytes") "concat") args
  | Expr.call (Expr.member (Expr.typeName Ty.bytes) "concat") args
  | Expr.call (Expr.member (Expr.ident "string") "concat") args
  | Expr.call (Expr.member (Expr.typeName Ty.string) "concat") args =>
      args.any (fun a =>
        match a with
        | Arg.positional e => Expr.abiArgNeedsEnvCleanup? e
        | Arg.named _ _ => false)
  | Expr.call (Expr.ident hname) [Arg.positional inner] =>
      (hname == "keccak256" || hname == "sha256" || hname == "ripemd160") &&
        Expr.abiBuiltinArgsNeedEnvCleanup inner
  | Expr.call (Expr.ident "ecrecover") args =>
      args.any (fun a =>
        match a with
        | Arg.positional e => Expr.abiArgNeedsEnvCleanup? e
        | Arg.named _ _ => false)
  -- WS1 (H): addmod/mulmod args and `new T[](len)`/`new bytes(len)` lengths
  -- carrying narrow checked arithmetic (Panic 0x11 at the operand width
  -- before the builtin/allocation) — reroutes the same statement positions
  -- (vardecl init, return) through the env-aware lowering, whose dedicated
  -- arms fire the cleanup.
  | Expr.call (Expr.ident amName)
      [Arg.positional amX, Arg.positional amY, Arg.positional amM] =>
      (amName == "addmod" || amName == "mulmod") &&
        (Expr.abiArgNeedsEnvCleanup? amX ||
          Expr.abiArgNeedsEnvCleanup? amY ||
          Expr.abiArgNeedsEnvCleanup? amM)
  | Expr.newExpr _ [Arg.positional lengthExpr] =>
      Expr.abiArgNeedsEnvCleanup? lengthExpr
  | _ => false

/-- R2 (env-lowering unification): recursion budget for the unified env-aware
    expression lowering. The recursion structurally decreases on every child
    (operands, branches, cast arguments, index keys), but the H2/NEG cast arms
    reach children through `peelToOverflowArithmetic?`/`peelToNarrowNeg?`
    (functions, not structural projections), so the mutual block is bounded by
    an explicit fuel instead of `sizeOf`. Mirrors `defaultAnnotateAbiFuel`; at
    fuel 0 the lowering degrades to the non-recursive
    `Expr.toCoreAsWithEnvDirect?` (today's fallback), never to a reject. -/
def defaultEnvLoweringFuel : Nat := 1024

/-- Build an index READ (`base[idx]`) from an already-lowered core index,
    mirroring exactly the `Expr.index` cases of `Expr.toCore?` (state-var
    `storageIndex`, `fixedBytesIndex` for a `bytesN` base, general `index`).
    Used by the MI1 internal-call-index hoist and (R2) by the narrow
    index-key env-aware lowering. -/
def Expr.indexReadCoreBuilder? (storageNames : List Name) (base : Expr) :
    Option (CoreExpr -> CoreExpr) :=
  match base with
  | Expr.ident name =>
      match stateNameRuntimeKey? name storageNames with
      | some key =>
          some (fun idx => SolidCore.Solidity.Source.Expr.storageIndex key idx)
      | none => do
          let baseCore ← Expr.toCore? storageNames (Expr.ident name)
          some (fun idx => SolidCore.Solidity.Source.Expr.index baseCore idx)
  | _ =>
      match Expr.abiTy? storageNames base with
      | some ty =>
          match Ty.fixedBytesSize? ty with
          | some size => do
              let baseCore ← Expr.toCore? storageNames base
              some (fun idx =>
                SolidCore.Solidity.Source.Expr.fixedBytesIndex size baseCore idx)
          | none => do
              let baseCore ← Expr.toCore? storageNames base
              some (fun idx => SolidCore.Solidity.Source.Expr.index baseCore idx)
      | none => do
          let baseCore ← Expr.toCore? storageNames base
          some (fun idx => SolidCore.Solidity.Source.Expr.index baseCore idx)

end SolidCore.Solidity.Executable
