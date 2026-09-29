import SolidCore.Solidity.Interface.Foundation

namespace SolidCore.Solidity.Executable

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

def Args.toExprsForParamNames? (paramNames : List (Option Name))
    (args : List Arg) : Option (List Expr) :=
  match Args.toPositionalExprs? args with
  | some exprs =>
      if paramNames.length == exprs.length then
        some exprs
      else
        none
  | none => do
      let names ← mapOption (fun name? => name?) paramNames
      if names.length == paramNames.length then
        Args.toNamedExprsForNames? names args
      else
        none

def FunctionDecl.isConstructor (decl : FunctionDecl) : Bool :=
  match decl.kind with
  | FunctionKind.constructor => true
  | _ => false

def ContractDecl.directStateVars (decl : ContractDecl) : List StateVarDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.stateVar stateVar => some stateVar
    | _ => none)

def StateVarDecl.isConstant (decl : StateVarDecl) : Bool :=
  match decl.mutability with
  | VarMutability.constant => true
  | _ => false

def ContractDecl.directFunctions (decl : ContractDecl) : List FunctionDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.function fn => some fn
    | _ => none)

def ContractDecl.directConstructors (decl : ContractDecl) : List FunctionDecl :=
  (ContractDecl.directFunctions decl).filter FunctionDecl.isConstructor

def ContractDecl.directConstructor? (decl : ContractDecl) :
    Option (Option FunctionDecl) :=
  match ContractDecl.directConstructors decl with
  | [] => some none
  | [ctor] => some (some ctor)
  | _ => none

-- `ContractDecls.contextualOrdinaryFunctions` and friends are defined further
-- below, after `ContractDecl.scopedConstantEntries` (they now inline each
-- contract's functions against that contract's OWN lexical constant scope, so
-- a derived contract's constant does not shadow a file-level constant read by
-- an inherited base function — see the C3 note there).

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

def ContractDecl.findByName? (contracts : List ContractDecl)
    (name : Name) : Option ContractDecl :=
  contracts.find? (fun decl => decl.name == name)

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

-- Contracts strictly after `decl` in a linearization (its more-derived
-- portion, in the same base->derived order as the input list).
def ContractDecls.afterDecl :
    List ContractDecl -> ContractDecl -> List ContractDecl
  | [], _ => []
  | c :: rest, decl =>
      if c.name == decl.name then rest
      else ContractDecls.afterDecl rest decl

-- Search `candidates` (most-derived first) for a contract whose constructor
-- carries a base-constructor modifier `baseDecl(args)`, returning the args and
-- the supplying contract (whose frame the args are evaluated in). solc allows
-- the constructor-modifier form on ANY derived contract, not just the direct
-- inheritor of `baseDecl`; the most-derived supplier wins (solc forbids
-- supplying a base's args twice, so at most one candidate matches).
def ContractDecl.baseConstructorModifierSupplier?
    (baseDecl : ContractDecl) :
    List ContractDecl -> Option (List Expr × ContractDecl)
  | [] => none
  | c :: rest =>
      match ContractDecl.baseConstructorModifierArgs? c baseDecl with
      | some (some args) => some (args, c)
      | _ => ContractDecl.baseConstructorModifierSupplier? baseDecl rest

-- Resolve a base contract's constructor arguments for deployment, together with
-- the contract that SUPPLIES them (whose constructor params/using-decls form
-- the frame in which the argument expressions are evaluated). solc permits a
-- base's constructor arguments to be given in two places:
--   (1) the inheritance-list specifier `contract C is B(expr)` — this must be
--       on the DIRECT inheritor of `baseDecl` (the immediate derived), and the
--       args are evaluated in that contract's frame; or
--   (2) a constructor modifier `constructor(...) B(expr)` — this may appear on
--       ANY derived contract in the linearization (e.g. the deployment target
--       naming an indirect base), and the args are evaluated in THAT contract's
--       frame. This is the OpenZeppelin pattern where the concrete harness
--       supplies an indirect base's args via a constructor modifier.
-- The most-derived supplier wins; solc forbids double specification.
def ContractDecl.baseConstructorArgsAndSupplier?
    (storageOrder : List ContractDecl) (baseDecl : ContractDecl) :
    Option (List Expr × ContractDecl) := do
  let immediateDerived ←
    ContractDecl.findImmediateDerivedInOrder? storageOrder baseDecl
  let spec ← ContractDecl.baseSpecifierFor? immediateDerived baseDecl
  let baseCtor? ← ContractDecl.directConstructor? baseDecl
  let baseParams :=
    match baseCtor? with
    | some ctor => ctor.params
    | none => []
  match spec.args with
  | _ :: _ =>
      -- Inline inheritance-specifier args on the direct inheritor.
      let args ← Args.toExprsForParams? baseParams spec.args
      some (args, immediateDerived)
  | [] =>
      -- No inline base-spec args: look for a constructor-modifier supplier
      -- anywhere more-derived than `baseDecl` (most-derived first).
      let candidates :=
        (ContractDecls.afterDecl storageOrder baseDecl).reverse
      match ContractDecl.baseConstructorModifierSupplier? baseDecl candidates with
      | some (args, supplier) => some (args, supplier)
      | none => some ([], immediateDerived)

def ContractDecl.baseDecls? (contracts : List ContractDecl)
    (decl : ContractDecl) : Option (List ContractDecl) :=
  mapOption
    (fun base => do
      let name ← pathLast? base.base
      ContractDecl.findByName? contracts name)
    decl.bases

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

/-- Storage / constructor / initializer order.

    solc lays out contract storage and runs base constructors + inline
    state-variable initializers in `reverse(linearizedBaseContracts)` order,
    i.e. reverse C3 = most-base-first (Types.cpp:2168-2172; C3 in
    NameAndTypeResolver.cpp:422-497 for solc v0.8.35).  `dispatchOrder?` is
    already the correct C3 linearization (most-derived-first), so storage
    order is simply its reverse.  Previously this used a separate naive
    left-to-right DFS post-order dedup traversal, which diverged from solc
    whenever a contract lists a direct base that is also an indirect base
    (DL1: e.g. `Z is Y, M` where `M is X, Y` swapped `x`/`y`). -/
def ContractDecl.storageOrder? (contracts : List ContractDecl)
    (decl : ContractDecl) : Option (List ContractDecl) :=
  (ContractDecl.dispatchOrder? contracts decl).map List.reverse

def BinaryOp.storageLayoutBaseEvalAllowed : BinaryOp -> Bool
  | BinaryOp.add
  | BinaryOp.sub
  | BinaryOp.mul
  | BinaryOp.div
  | BinaryOp.mod
  | BinaryOp.exp
  | BinaryOp.bitAnd
  | BinaryOp.bitOr
  | BinaryOp.bitXor
  | BinaryOp.shl
  | BinaryOp.shr
  | BinaryOp.sar => true
  | _ => false

end SolidCore.Solidity.Executable
