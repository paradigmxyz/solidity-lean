import SolidCore.Solidity.Ast
import Verify.HirShadow.Facts

/-!
# Agreement of HIR shadow facts with the independent source model

`check sel c f` derives, from the solc-AST source model `c` alone, the facts `Facts.lean` states:
the storage layout of its value-typed state variables (solc's packing rule: a variable starts a new
slot when it does not fit in the rest of the current one; constants and immutables take none), and
for each function, public getter and constructor its kind, canonical signature, visibility,
mutability and ABI types, with the selector `sel signature` for external and public ones. The
facts are accepted only if they are exactly that list, in declaration order.

`sel` is Keccak-256's selector in every use (`Counter.lean` rewrites it to a kernel-checked table).

Verdicts:
- `agree`: every derived fact equals solar's.
- `rejected`: a fact differs, or the facts are for another version or contract.
- `blocked`: the contract is outside the envelope this check covers (inheritance, non-value state
  variables, modifiers, events, errors, user types, receive or fallback, ...). Blocked is never
  agreement.

This is an agreement check of two independent frontends on interface facts, not a proof that
either one is right, and it reads no function body.
-/

namespace Verify.HirShadow
open SolidCore.Solidity

inductive Verdict where
  | agree
  | rejected (why : String)
  | blocked (why : String)
  deriving DecidableEq, Repr

def Verdict.isAgree : Verdict → Bool
  | .agree => true
  | _ => false

/-- The canonical ABI name of a value type inside the envelope. -/
def canon : Ty → Option String
  | .bool => some "bool"
  | .address _ => some "address"
  | .uint n => if n % 8 = 0 ∧ 8 ≤ n ∧ n ≤ 256 then some ("uint" ++ toString n) else none
  | .int n => if n % 8 = 0 ∧ 8 ≤ n ∧ n ≤ 256 then some ("int" ++ toString n) else none
  | .bytesN n => if 1 ≤ n ∧ n ≤ 32 then some ("bytes" ++ toString n) else none
  | _ => none

/-- Its size in storage, in bytes. -/
def size : Ty → Option Nat
  | .bool => some 1
  | .address _ => some 20
  | .uint n => some (n / 8)
  | .int n => some (n / 8)
  | .bytesN n => some n
  | _ => none

def canonAll (ps : List Parameter) : Option (List String) :=
  ps.mapM fun p => canon p.ty

def visName : Option Visibility → Option String
  | some .public_ => some "public"
  | some .external_ => some "external"
  | some .internal_ => some "internal"
  | some .private_ => some "private"
  | none => none

def mutName : StateMutability → String
  | .pure => "pure"
  | .view => "view"
  | .nonpayable => "nonpayable"
  | .payable => "payable"

def sigOf (name : String) (ins : List String) : String :=
  name ++ "(" ++ ",".intercalate ins ++ ")"

/-- Storage layout of the state variables, from slot `slot` at byte `off`. -/
def layout : List StateVarDecl → Nat → Nat → Except String (List StateVarFact)
  | [], _, _ => .ok []
  | v :: vs, slot, off =>
    match v.mutability with
    | .constant | .immutable => layout vs slot off
    | .transient => .error ("transient state variable " ++ v.name)
    | .mutable =>
      match canon v.ty, size v.ty with
      | some t, some n =>
        let s := if off + n > 32 then slot + 1 else slot
        let o := if off + n > 32 then 0 else off
        (layout vs s (o + n)).map fun rest =>
          ({ name := v.name, type := t, slot := s, offset := o, bytes := n } : StateVarFact) :: rest
      | _, _ => .error ("state variable " ++ v.name ++ " is not of a value type")

/-- One item's function facts: a function, a public getter or the constructor. -/
def itemFacts (sel : String → Nat) : ContractItem → Except String (List FunctionFact)
  | .stateVar v =>
    match v.visibility with
    | some .public_ =>
      match canon v.ty with
      | some t =>
        .ok [{ kind := "getter", name := v.name, signature := sigOf v.name [],
               selector := some (sel (sigOf v.name [])), visibility := "external",
               mutability := "view", inputs := [], outputs := [t] }]
      | none => .error ("public getter of " ++ v.name ++ " is not of a value type")
    | _ => .ok []
  | .function f =>
    match f.kind, f.name, visName f.visibility, canonAll f.params, canonAll f.returns with
    | .function, some n, some vis, some ins, some outs =>
      if f.modifiers.isEmpty then
        let sig := sigOf n ins
        let s := if vis = "external" ∨ vis = "public" then some (sel sig) else none
        .ok [{ kind := "function", name := n, signature := sig, selector := s, visibility := vis,
               mutability := mutName f.mutability, inputs := ins, outputs := outs }]
      else .error ("function " ++ n ++ " has modifiers")
    | .constructor, _, vis?, some ins, some [] =>
      .ok [{ kind := "constructor", name := "constructor", signature := sigOf "constructor" ins,
             selector := none, visibility := vis?.getD "public", mutability := mutName f.mutability,
             inputs := ins, outputs := [] }]
    | .receive, _, _, _, _ => .error "receive function"
    | .fallback, _, _, _, _ => .error "fallback function"
    | _, n, _, _, _ => .error ("function " ++ n.getD "?" ++ " has a type outside the envelope")
  | .modifierDecl _ => .error "modifier declaration"
  | .eventDecl _ => .error "event declaration"
  | .errorDecl _ => .error "error declaration"
  | .structDecl _ => .error "struct declaration"
  | .enumDecl _ => .error "enum declaration"
  | .userValueTypeDecl _ => .error "user-defined value type"
  | .usingDecl _ => .error "using directive"

def stateVars : List ContractItem → List StateVarDecl
  | [] => []
  | .stateVar v :: is => v :: stateVars is
  | _ :: is => stateVars is

/-- What the source model says, or why it is outside the envelope. -/
def model (sel : String → Nat) (c : ContractDecl) :
    Except String (List StateVarFact × List FunctionFact) := do
  if c.kind != .contract then throw "not a plain contract"
  if c.abstract then throw "abstract contract"
  if !c.bases.isEmpty then throw "inheritance"
  if c.layoutBase.isSome then throw "custom storage layout"
  let vars ← layout (stateVars c.items) 0 0
  let fns ← c.items.mapM (itemFacts sel)
  return (vars, fns.flatten)

/-- The first position where two lists differ, with the name of the derived entry there. -/
def firstDiff {α} [DecidableEq α] (name : α → String) : List α → List α → Nat → String
  | [], [], _ => "none"
  | a :: _, [], i => toString i ++ " (" ++ name a ++ " missing from the facts)"
  | [], b :: _, i => toString i ++ " (" ++ name b ++ " not in the source)"
  | a :: as, b :: bs, i => if a = b then firstDiff name as bs (i + 1) else toString i ++ " (" ++ name a ++ ")"

def check (sel : String → Nat) (c : ContractDecl) (f : Facts) : Verdict :=
  if f.version ≠ 1 then .rejected ("facts version " ++ toString f.version)
  else if f.contract ≠ c.name then .rejected ("facts of contract " ++ f.contract)
  else match model sel c with
    | .error why => .blocked why
    | .ok (vars, fns) =>
      if vars ≠ f.stateVars then
        .rejected ("storage differs at " ++ firstDiff StateVarFact.name vars f.stateVars 0)
      else if fns ≠ f.functions then
        .rejected ("functions differ at " ++ firstDiff FunctionFact.name fns f.functions 0)
      else .agree

end Verify.HirShadow
