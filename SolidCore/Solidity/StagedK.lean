import SolidCore.Solidity.Staged

/-!
# Staged translation checks: kernel-cheap equal forms and assembly lemmas

Equal forms of functions the translation calls (`TypeEnv.shadowedStateNames_eq_K`,
`stringDecEq_eq_K`, `toByteArray_eq_K`) for `kernel_rfl … using`, and the lemmas that assemble a
contract's translation from its context, its function groups (each from its functions'
translations) and its assembly, each checked in a module of its own.
-/


namespace SolidCore.Solidity.Executable

/-! ### Kernel-cheap equal forms

The kernel evaluates a string comparison by expanding both literals to their UTF-8 bytes and
comparing them byte by byte, so `TypeEnv.shadowedStateNames`, which compares every pair of a type
environment's names and runs at every statement the lowering visits, costs gigabytes under a
contract whose environment holds many long `__external_call_kind:` keys. `bytesKey` and
`nameKey` number a string by its bytes injectively, so the kernel compares two names as two
numbers; `TypeEnv.shadowedStateNames_eq_K` and `stringDecEq_eq_K` let `kernel_rfl … using`
evaluate the translation with these equal forms. -/

/-- A byte list as a number: its bytes are the base-257 digits 1..256. -/
def bytesKey (l : List UInt8) : Nat := l.foldr (fun b acc => b.toNat + 1 + 257 * acc) 0

theorem bytesKey_inj : ∀ {l₁ l₂ : List UInt8}, bytesKey l₁ = bytesKey l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], c :: cs, h => by simp [bytesKey] at h; omega
  | b :: bs, [], h => by simp [bytesKey] at h
  | b :: bs, c :: cs, h => by
    have hb := UInt8.toNat_lt b
    have hc := UInt8.toNat_lt c
    simp only [bytesKey, List.foldr_cons] at h
    have h1 : b.toNat = c.toNat := by omega
    have h2 : bytesKey bs = bytesKey cs := by unfold bytesKey; omega
    rw [bytesKey_inj h2, UInt8.toNat_inj.mp h1]

/-- A string as a number: its UTF-8 bytes by `bytesKey`. -/
def nameKey (s : String) : Nat := bytesKey s.toByteArray.data.toList

theorem nameKey_inj {s₁ s₂ : String} (h : nameKey s₁ = nameKey s₂) : s₁ = s₂ := by
  have h' := bytesKey_inj h
  rcases s₁ with ⟨⟨⟨l₁⟩⟩, p₁⟩
  rcases s₂ with ⟨⟨⟨l₂⟩⟩, p₂⟩
  simp at h'
  subst h'
  rfl

/-- `TypeEnv.shadowedStateNames`, comparing names by `nameKey`. -/
def TypeEnv.shadowedStateNamesK (env : TypeEnv) : List Name :=
  let keyed := (env.map Prod.fst).map (fun n => (n, nameKey n))
  (keyed.filter (fun p => (keyed.filter (fun q => q.2 == p.2)).length ≥ 2)).map Prod.fst

theorem TypeEnv.shadowedStateNames_eq_K :
    TypeEnv.shadowedStateNames = TypeEnv.shadowedStateNamesK := by
  funext env
  have hk : ∀ m n : Name, (nameKey m == nameKey n) = (m == n) := by
    intro m n
    by_cases h : m = n
    · subst h; simp
    · have : nameKey m ≠ nameKey n := fun e => h (nameKey_inj e)
      simp [h, this]
  simp only [TypeEnv.shadowedStateNames, TypeEnv.shadowedStateNamesK, List.filter_map,
    List.map_map, Function.comp_def, List.length_map, hk]

/-- String equality decided by `nameKey`. -/
def stringDecEqK (a b : String) : Decidable (a = b) :=
  if h : nameKey a = nameKey b then isTrue (nameKey_inj h) else isFalse (fun e => h (e ▸ rfl))

theorem stringDecEq_eq_K : String.decEq = stringDecEqK := by
  funext a b; exact Subsingleton.elim _ _

/-! ### Assembling the staged checks -/

-- The unused-variables linter takes gigabytes on this many hypotheses.
set_option linter.unusedVariables false in
/-- A context the translation computes, from its fields one by one. -/
theorem FromOrdersCtx.some_eq_of_fields {o : Option FromOrdersCtx} {c : FromOrdersCtx}
    (h0 : Option.map FromOrdersCtx.allContracts o = some c.allContracts)
    (h1 : Option.map FromOrdersCtx.sourceUsingDecls o = some c.sourceUsingDecls)
    (h2 : Option.map FromOrdersCtx.sourceFunctions o = some c.sourceFunctions)
    (h3 : Option.map FromOrdersCtx.dispatchOrder o = some c.dispatchOrder)
    (h4 : Option.map FromOrdersCtx.structEnv o = some c.structEnv)
    (h5 : Option.map FromOrdersCtx.stateVars o = some c.stateVars)
    (h6 : Option.map FromOrdersCtx.constants o = some c.constants)
    (h7 : Option.map FromOrdersCtx.storageStateVars o = some c.storageStateVars)
    (h8 : Option.map FromOrdersCtx.transientStateVars o = some c.transientStateVars)
    (h9 : Option.map FromOrdersCtx.storageNames o = some c.storageNames)
    (h10 : Option.map FromOrdersCtx.layoutBaseSlot o = some c.layoutBaseSlot)
    (h11 : Option.map FromOrdersCtx.externalCallKindEnv o = some c.externalCallKindEnv)
    (h12 : Option.map FromOrdersCtx.externalCallKindTypeEnv o = some c.externalCallKindTypeEnv)
    (h13 : Option.map FromOrdersCtx.stateEnv o = some c.stateEnv)
    (h14 : Option.map FromOrdersCtx.sharedConstantTail o = some c.sharedConstantTail)
    (h15 : Option.map FromOrdersCtx.modifiers o = some c.modifiers)
    (h16 : Option.map FromOrdersCtx.libraryHelpers o = some c.libraryHelpers)
    (h17 : Option.map FromOrdersCtx.baseHelpers o = some c.baseHelpers)
    (h18 : Option.map FromOrdersCtx.superHelpers o = some c.superHelpers)
    (h19 : Option.map FromOrdersCtx.availableFunctions o = some c.availableFunctions)
    (h20 : Option.map FromOrdersCtx.internalFnIds o = some c.internalFnIds)
    (h21 : Option.map FromOrdersCtx.contractEvents o = some c.contractEvents)
    (h22 : Option.map FromOrdersCtx.visibleSourceEvents o = some c.visibleSourceEvents)
    (h23 : Option.map FromOrdersCtx.contractErrors o = some c.contractErrors)
    (h24 : Option.map FromOrdersCtx.visibleSourceErrors o = some c.visibleSourceErrors)
    (h25 : Option.map FromOrdersCtx.eventArgEnv o = some c.eventArgEnv)
    (h26 : Option.map FromOrdersCtx.eventIndexedEnv o = some c.eventIndexedEnv)
    (h27 : Option.map FromOrdersCtx.errorArgEnv o = some c.errorArgEnv) :
    o = some c := by
  cases o with
  | none => exact absurd h0 (by simp)
  | some x =>
    have e0 : x.allContracts = c.allContracts := Option.some.inj h0
    have e1 : x.sourceUsingDecls = c.sourceUsingDecls := Option.some.inj h1
    have e2 : x.sourceFunctions = c.sourceFunctions := Option.some.inj h2
    have e3 : x.dispatchOrder = c.dispatchOrder := Option.some.inj h3
    have e4 : x.structEnv = c.structEnv := Option.some.inj h4
    have e5 : x.stateVars = c.stateVars := Option.some.inj h5
    have e6 : x.constants = c.constants := Option.some.inj h6
    have e7 : x.storageStateVars = c.storageStateVars := Option.some.inj h7
    have e8 : x.transientStateVars = c.transientStateVars := Option.some.inj h8
    have e9 : x.storageNames = c.storageNames := Option.some.inj h9
    have e10 : x.layoutBaseSlot = c.layoutBaseSlot := Option.some.inj h10
    have e11 : x.externalCallKindEnv = c.externalCallKindEnv := Option.some.inj h11
    have e12 : x.externalCallKindTypeEnv = c.externalCallKindTypeEnv := Option.some.inj h12
    have e13 : x.stateEnv = c.stateEnv := Option.some.inj h13
    have e14 : x.sharedConstantTail = c.sharedConstantTail := Option.some.inj h14
    have e15 : x.modifiers = c.modifiers := Option.some.inj h15
    have e16 : x.libraryHelpers = c.libraryHelpers := Option.some.inj h16
    have e17 : x.baseHelpers = c.baseHelpers := Option.some.inj h17
    have e18 : x.superHelpers = c.superHelpers := Option.some.inj h18
    have e19 : x.availableFunctions = c.availableFunctions := Option.some.inj h19
    have e20 : x.internalFnIds = c.internalFnIds := Option.some.inj h20
    have e21 : x.contractEvents = c.contractEvents := Option.some.inj h21
    have e22 : x.visibleSourceEvents = c.visibleSourceEvents := Option.some.inj h22
    have e23 : x.contractErrors = c.contractErrors := Option.some.inj h23
    have e24 : x.visibleSourceErrors = c.visibleSourceErrors := Option.some.inj h24
    have e25 : x.eventArgEnv = c.eventArgEnv := Option.some.inj h25
    have e26 : x.eventIndexedEnv = c.eventIndexedEnv := Option.some.inj h26
    have e27 : x.errorArgEnv = c.errorArgEnv := Option.some.inj h27
    have hx : x = ⟨x.allContracts, x.sourceUsingDecls, x.sourceFunctions, x.dispatchOrder, x.structEnv, x.stateVars, x.constants, x.storageStateVars, x.transientStateVars, x.storageNames, x.layoutBaseSlot, x.externalCallKindEnv, x.externalCallKindTypeEnv, x.stateEnv, x.sharedConstantTail, x.modifiers, x.libraryHelpers, x.baseHelpers, x.superHelpers, x.availableFunctions, x.internalFnIds, x.contractEvents, x.visibleSourceEvents, x.contractErrors, x.visibleSourceErrors, x.eventArgEnv, x.eventIndexedEnv, x.errorArgEnv⟩ := rfl
    have hc : c = ⟨c.allContracts, c.sourceUsingDecls, c.sourceFunctions, c.dispatchOrder, c.structEnv, c.stateVars, c.constants, c.storageStateVars, c.transientStateVars, c.storageNames, c.layoutBaseSlot, c.externalCallKindEnv, c.externalCallKindTypeEnv, c.stateEnv, c.sharedConstantTail, c.modifiers, c.libraryHelpers, c.baseHelpers, c.superHelpers, c.availableFunctions, c.internalFnIds, c.contractEvents, c.visibleSourceEvents, c.contractErrors, c.visibleSourceErrors, c.eventArgEnv, c.eventIndexedEnv, c.errorArgEnv⟩ := rfl
    rw [hx, hc, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27]

/-- The contract translation from its context, function groups and assembly. -/
theorem ContractDecl.toCoreFromOrders?_of_stages {allContracts : List ContractDecl}
    {sourceUsingDecls : List UsingDecl} {sourceFunctions : List FunctionDecl}
    {sourceEvents : List EventDecl} {sourceErrors : List ErrorDecl}
    {sourceConstants : List StateVarDecl} {sourceUserValueTypes : List UserValueTypeDecl}
    {sourceEnums : List EnumDecl} {sourceStructs : List StructDecl}
    {storageOrder dispatchOrder : List ContractDecl} {c : FromOrdersCtx}
    {groups : List (List CoreFunctionDef)} {core : CoreContract}
    (hc : ContractDecl.fromOrdersCtx? allContracts sourceUsingDecls sourceFunctions sourceEvents
      sourceErrors sourceConstants sourceUserValueTypes sourceEnums sourceStructs storageOrder
      dispatchOrder = some c)
    (hg : mapOption c.group? c.dispatchOrder = some groups)
    (ha : c.assemble? groups = some core) :
    ContractDecl.toCoreFromOrders? allContracts sourceUsingDecls sourceFunctions sourceEvents
      sourceErrors sourceConstants sourceUserValueTypes sourceEnums sourceStructs storageOrder
      dispatchOrder = some core := by
  unfold ContractDecl.toCoreFromOrders?
  rw [hc]
  show (mapOption c.group? c.dispatchOrder).bind c.assemble? = some core
  rw [hg]
  exact ha

/-- info: 'SolidCore.Solidity.Executable.TypeEnv.shadowedStateNames_eq_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TypeEnv.shadowedStateNames_eq_K

/-- info: 'SolidCore.Solidity.Executable.stringDecEq_eq_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stringDecEq_eq_K

/-- info: 'SolidCore.Solidity.Executable.FromOrdersCtx.some_eq_of_fields' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FromOrdersCtx.some_eq_of_fields

/-- info: 'SolidCore.Solidity.Executable.ContractDecl.toCoreFromOrders?_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContractDecl.toCoreFromOrders?_of_stages

end SolidCore.Solidity.Executable

namespace SolidCore.Solidity.Executable

/-! ### A function group from its functions -/

/-- The functions of a contract that `ContractDecl.directCoreFunctions?` translates. -/
def FromOrdersCtx.fnsOf (decl : ContractDecl) : List FunctionDecl :=
  (ContractDecl.directOrdinaryFunctions decl).filter
    (fun fn => (FunctionDecl.isCoreEntrypoint fn || FunctionDecl.isBoundaryCallee fn) && fn.body.isSome)

/-- The translation of one function of a contract in the context, as `FromOrdersCtx.group?` does. -/
def FromOrdersCtx.pairF (c : FromOrdersCtx) (decl : ContractDecl) (fn : FunctionDecl) :
    Option (FunctionDecl × CoreFunctionDef) :=
  ContractDecl.directCoreFunctionPair? c.storageNames
    (ContractDecl.scopedConstantEnv c.dispatchOrder c.sharedConstantTail decl)
    c.stateEnv c.externalCallKindEnv c.allContracts c.dispatchOrder
    (ContractDecl.directUsingDecls decl ++ c.sourceUsingDecls) c.modifiers c.availableFunctions
    c.sourceFunctions c.eventArgEnv c.errorArgEnv c.internalFnIds c.eventIndexedEnv
    (c.contractEvents ++ c.visibleSourceEvents) decl fn

/-- The public state variables' getters of a contract in the context. -/
def FromOrdersCtx.getters? (c : FromOrdersCtx) (decl : ContractDecl) : Option (List CoreFunctionDef) :=
  filterMapOption
    (StateVarDecl.toCoreGetterIfPublic? c.storageNames
      (ContractDecl.scopedConstantEnv c.dispatchOrder c.sharedConstantTail decl))
    (ContractDecl.directStateVars decl)

/-- A function group from its getters and its functions' translations. -/
def groupOfPairs (getters : List CoreFunctionDef) (pairs : List (FunctionDecl × CoreFunctionDef)) :
    List CoreFunctionDef :=
  getters ++ (pairs.filter (fun pair => FunctionDecl.isCoreEntrypoint pair.fst)).map Prod.snd ++
    pairs.filterMap (fun pair =>
      if FunctionDecl.isBoundaryCallee pair.fst then
        (FunctionDecl.internalTableKey? pair.fst).map
          (fun key => { pair.snd with name := key, selector? := none })
      else none)

/-- `FromOrdersCtx.group?` is its getters and its functions' translations, one by one. -/
theorem FromOrdersCtx.group?_of_pairs {c : FromOrdersCtx} {decl : ContractDecl}
    {getters : List CoreFunctionDef} {pairs : List (FunctionDecl × CoreFunctionDef)}
    (hg : c.getters? decl = some getters)
    (hp : mapOption (c.pairF decl) (FromOrdersCtx.fnsOf decl) = some pairs) :
    c.group? decl = some (groupOfPairs getters pairs) := by
  have e : c.group? decl = (c.getters? decl).bind (fun g =>
      (mapOption (c.pairF decl) (FromOrdersCtx.fnsOf decl)).bind
        (fun ps => some (groupOfPairs g ps))) := rfl
  rw [e, hg, hp]
  rfl

theorem mapOption_nil' {α β : Type} (f : α → Option β) : mapOption f [] = some [] := rfl

theorem mapOption_cons' {α β : Type} {f : α → Option β} {x : α} {xs : List α} {y : β} {ys : List β}
    (h : f x = some y) (hs : mapOption f xs = some ys) : mapOption f (x :: xs) = some (y :: ys) := by
  simp only [mapOption, h, hs, bind, Option.bind]

/-- info: 'SolidCore.Solidity.Executable.FromOrdersCtx.group?_of_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FromOrdersCtx.group?_of_pairs

end SolidCore.Solidity.Executable

namespace SolidCore.Solidity.Executable

/-- `List.toByteArray` as one constructor application, without its pushes: the kernel builds a
string literal's bytes through `List.toByteArray`, whose pushes copy the list once per byte. -/
def toByteArrayK (bs : List UInt8) : ByteArray := ⟨⟨bs⟩⟩

theorem toByteArray_loop : ∀ (bs : List UInt8) (r : ByteArray),
    List.toByteArray.loop bs r = ⟨⟨r.data.toList ++ bs⟩⟩
  | [], ⟨⟨l⟩⟩ => by simp [List.toByteArray.loop]
  | b :: bs, r => by
    rw [List.toByteArray.loop, toByteArray_loop bs]
    cases r with
    | mk a => cases a with
      | mk l => simp [ByteArray.push, Array.push]

theorem toByteArray_eq_K : List.toByteArray = toByteArrayK := by
  funext bs
  simp [List.toByteArray, toByteArray_loop, toByteArrayK, ByteArray.empty, ByteArray.emptyWithCapacity] <;> rfl

/-- info: 'SolidCore.Solidity.Executable.toByteArray_eq_K' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms toByteArray_eq_K

end SolidCore.Solidity.Executable
