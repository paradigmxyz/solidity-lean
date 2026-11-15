/-!
# HIR shadow facts (format version 1)

What solar's analysis says about one contract's interface: its state variables with their storage
slots, and its functions and public getters with canonical signatures and selectors. solar writes
them (`tools/hir-shadow/hir_shadow.py` in solar, from its HIR-backed outputs) as JSON and as a Lean
term of these types.

The facts are untrusted hints. Nothing here is a frontend or a semantics: `Verify.HirShadow.check`
compares them with what the independent source model (the solc-AST import, `ContractDecl`) says,
and only agreement is accepted. A change of a field or its meaning is a new `version`.
-/

namespace Verify.HirShadow

/-- A state variable that occupies storage: canonical type, slot, byte offset and size. -/
structure StateVarFact where
  name : String
  type : String
  slot : Nat
  offset : Nat
  bytes : Nat
  deriving DecidableEq, Repr

/-- A function, public getter or constructor. `kind` is `function`, `getter` or `constructor`;
`selector` is present exactly for external and public functions and getters. -/
structure FunctionFact where
  kind : String
  name : String
  signature : String
  selector : Option Nat
  visibility : String
  mutability : String
  inputs : List String
  outputs : List String
  deriving DecidableEq, Repr

/-- One contract's facts and what binds them to a run. -/
structure Facts where
  version : Nat
  solarCommit : String
  solarBinarySha256 : String
  source : String
  sourceSha256 : String
  contract : String
  stateVars : List StateVarFact
  functions : List FunctionFact
  deriving Repr

end Verify.HirShadow
