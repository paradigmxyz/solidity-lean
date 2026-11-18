import Verify.Shapes
import SolidCore.Refinement.Generic.StageFrom
import SolidCore.Refinement.Solar.AssembleCtxGasFrom

/-!
# The one expected theorem of a certified contract

Every supported contract is certified against the same statement, `Generic.Expected src spec
bytes`, whatever the contract: no shape is chosen by the contract's name and no fixture is
selected. Its three parameters are the only per-contract inputs:

* `src : Source ws`: SolidCore's type check of solc's AST of the source unit
  (`scripts/solc_ast_to_lean_source.py`'s `importedSourceUnit`) and the contract's name, at a
  fuel, deployed with the constructor argument words `ws` (`Source.ctorArgs`, by default `[]`:
  `Source` alone is `Source []`). This independent source semantics is the source of truth;
  solar's HIR or MIR appears only inside proofs, as a stage checked against it.
* `spec : Spec`: the coverage (which contexts, which entrypoints), the valid calls, allowed
  statuses, postcondition and gas bound, each a function of the context, and the named
  assumptions the statement is conditional on.
* `bytes : List Nat`: the exact runtime bytes the driver's own solar emitted in this run.

## Constructor arguments

The argument words are part of the source's type, so they are an input of the statement, not a
witness inside it: `src.semAt ctx` runs every call against the contract that SolidCore's
constructor leaves on exactly `src.ctorArgs` (`solidCoreFromArgs`, the Lifecycle tier's
constructor call). With `[]` it is `solidCoreFrom`, by `rfl` (`Source.semAt_nil`), so every
existing statement keeps its meaning. The deployment frame (sender `selfAddress`, no value) is
not the call's: a `Context` is the runtime frame only. That the words are the ones the creation
code carries is `Source.CreatedBy` (SolidCore/Refinement/Generic/Statement.lean).

## One parametric context

A `Context` is the frame a call runs in. Its caller is a parameter of both semantics (SolidCore's
`solidCoreFrom`, EthLib's `runWithFrom`); the contract's own address (`selfAddress`), the block
and the transaction are those of `Target.message` and are part of the recorded coverage, not
parameters (docs/SUPPORTED_ENVELOPE.md). `spec.Contexts` says which contexts the statement covers;
a statement for one caller only covers less, and the coverage says so: there is no separate
"fixed-caller" family of statements.

## What `Expected` states

1. `bytes` are bytes (each below 256), so `runtimeCode bytes` is exactly them;
2. `spec.Covered`: the coverage is inhabited and checked in the same context: some context is
   covered, every covered context is a real one (a caller below `2 ^ 160` other than the
   contract), and for every covered context and every declared entrypoint some valid call of
   that entrypoint exists in that context (so no entrypoint's premise is unsatisfiable), the
   postcondition rejects some result of a valid call and the allowed statuses reject some revert
   of a valid call;
3. under the named assumptions `spec.assumptions` (none: the unconditional tier; some: the
   conditional tier, each one a hypothesis of the statement), in every covered context,
   `CertifiedAt`: the source translation (equivalence at every gas, termination, resources) and
   the specification's proof (allowed statuses and postcondition of every source result),
   composed on the same source semantics, program and valid calls.

**Resources and out-of-gas.** `ResourcesAt` states that from `spec.gas call` gas on the bytes give
exactly the source's observable. An observable does not carry EthLib's error kind
(`Final.Target.runMsg` keeps only `evm.error.isNone`), so where the source reverts with empty data
this equality does not by itself exclude an out-of-gas halt with the same observable. It is an
observable-equality bound, not a no-out-of-gas guarantee; nothing here claims the bytes fail
below it.

**Tier.** `Expected` is the runtime tier: every valid call from any storage the spec admits. It
does not state that a constructor establishes the invariant a specification's precondition
assumes, nor that every entrypoint preserves it, nor anything about reentrant calls; a lifecycle
certificate is a separate tier (docs/SUPPORTED_ENVELOPE.md).
-/

namespace SolidCore.Verify.Generic

open SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Solidity

/-! ## Source, context, specification -/

/-- **The source**: solc's AST of the source unit, the contract's name and SolidCore's fuel, for a
deployment with the constructor argument words `ctorArgs` (by default none). -/
structure Source (ctorArgs : List Nat := []) where
  unit : SourceUnit
  contract : String
  fuel : Nat

/-- The constructor argument words of the source's deployment. -/
def Source.ctorArgs {ws : List Nat} (_ : Source ws) : List Nat := ws

/-- The same source unit, contract and fuel, deployed with the argument words `ws`. -/
def Source.withArgs {ws₀ : List Nat} (src : Source ws₀) (ws : List Nat) : Source ws :=
  ⟨src.unit, src.contract, src.fuel⟩

/-- SolidCore's checked contract of the source: the type checker over solc's AST. -/
def Source.checked {ws : List Nat} (src : Source ws) :
    Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract src.unit src.contract

/-- **The frame of a call**: its caller. The contract's address, the block and the transaction
are `Target.message`'s. -/
structure Context where
  caller : Nat
  deriving DecidableEq

/-- A real context: an account address other than the contract's. -/
def Context.Ok (ctx : Context) : Prop := ctx.caller < 2 ^ 160 ∧ ctx.caller ≠ selfAddress

/-- The context every existing single-frame statement is about. -/
def Context.default : Context := ⟨callerAddress⟩

theorem Context.default_ok : Context.default.Ok := by
  unfold Context.Ok Context.default callerAddress selfAddress; decide

/-- SolidCore at the source's fuel, on calls sent in `ctx` to the contract deployed with the
source's argument words. -/
abbrev Source.semAt {ws : List Nat} (src : Source ws) (ctx : Context) : Sem :=
  solidCoreFromArgs ctx.caller src.fuel ws

/-- With no argument words, `semAt` is `solidCoreFrom`: the same statement as before arguments. -/
theorem Source.semAt_nil (src : Source) (ctx : Context) :
    src.semAt ctx = solidCoreFrom ctx.caller src.fuel :=
  rfl

/-- Changing only the argument words changes only the deployment. -/
theorem Source.semAt_withArgs {ws₀ : List Nat} (src : Source ws₀) (ws : List Nat) (ctx : Context) :
    (src.withArgs ws).semAt ctx = solidCoreFromArgs ctx.caller src.fuel ws :=
  rfl

/-- EthLib's run of the bytes in `ctx` with `gas` gas. -/
def runAt (ctx : Context) (gas : Nat) (code : ByteArray) (call : Call) : Option Observable :=
  Final.Target.runWithFrom ctx.caller gas code call

/-- **The specification**, every part a function of the context. -/
structure Spec where
  /-- The contexts the statement covers. -/
  Contexts : Context → Prop
  /-- The declared entrypoints: a name and the calls of it (its selector and premise). -/
  entries : List (String × (Context → Call → Prop))
  Valid : Context → Call → Prop
  Allowed : Context → Call → Observable → Prop
  Post : Context → Call → Observable → Prop
  gas : Context → Call → Nat
  /-- Named assumptions the statement is conditional on (empty: unconditional). -/
  assumptions : List Prop

/-- **Coverage checked in the same context** (the module docstring, item 2). -/
def Spec.Covered (spec : Spec) : Prop :=
  (∃ ctx, spec.Contexts ctx) ∧
  (∀ ctx, spec.Contexts ctx → ctx.Ok) ∧
  (∀ ctx, spec.Contexts ctx → ∀ e ∈ spec.entries, ∃ call, spec.Valid ctx call ∧ e.2 ctx call) ∧
  (∃ ctx call obs, spec.Contexts ctx ∧ spec.Valid ctx call ∧ ¬ spec.Post ctx call obs) ∧
  (∃ ctx call obs, spec.Contexts ctx ∧ spec.Valid ctx call ∧ obs.success = false ∧
    ¬ spec.Allowed ctx call obs)

/-- The statement's assumptions all hold. -/
def Spec.Assumed (spec : Spec) : Prop := ∀ A ∈ spec.assumptions, A

/-! ## The obligations in a context -/

/-- Equivalence at every gas below `2 ^ 256` in `ctx`. -/
def EquivAt (S : Sem) (p : S.Prog) (ctx : Context) (code : ByteArray) (Valid : Call → Prop) :
    Prop :=
  ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call → ∀ obs, runAt ctx gas code call = some obs →
    S.run p call = some obs ∨ Inert call obs

/-- Resources in `ctx`: from `G call` gas on the bytes give exactly the source's observable. -/
def ResourcesAt (S : Sem) (p : S.Prog) (ctx : Context) (code : ByteArray) (Valid : Call → Prop)
    (G : Call → Nat) : Prop :=
  ∀ call, Valid call → G call < 2 ^ 64 ∧
    ∀ gas, G call ≤ gas → gas < 2 ^ 256 → runAt ctx gas code call = S.run p call

/-- **The source translation in a context**, with no user specification: equivalence, termination
with any status and resources, on an inhabited set of calls. -/
structure TranslationAt (S : Sem) (p : S.Prog) (ctx : Context) (code : ByteArray)
    (Valid : Call → Prop) (G : Call → Nat) : Prop where
  inhabited : ∃ call, Valid call
  equiv : EquivAt S p ctx code Valid
  terminates : Terminates S p Valid (fun _ _ => True)
  resources : ResourcesAt S p ctx code Valid G

/-- **The user specification's proof**, of the same source semantics, with no bytes. -/
structure SpecProof (S : Sem) (p : S.Prog) (Valid : Call → Prop)
    (Allowed Post : Call → Observable → Prop) : Prop where
  allowed : ∀ call, Valid call → ∀ obs, S.run p call = some obs → Allowed call obs
  meets : Meets S p Valid Post

/-- **Certified in a context**: the translation and the specification's proof, on the same source
semantics, program and valid calls. -/
structure CertifiedAt (S : Sem) (p : S.Prog) (ctx : Context) (code : ByteArray)
    (Valid : Call → Prop) (Allowed Post : Call → Observable → Prop) (G : Call → Nat) : Prop where
  translation : TranslationAt S p ctx code Valid G
  spec : SpecProof S p Valid Allowed Post

/-- The runtime code of a list of bytes. -/
def runtimeCode (bytes : List Nat) : ByteArray := ⟨(bytes.map UInt8.ofNat).toArray⟩

/-! ## The expected theorem -/

/-- **The expected theorem**, the same for every supported contract. -/
def Expected {ws : List Nat} (src : Source ws) (spec : Spec) (bytes : List Nat) : Prop :=
  bytes.all (· < 256) = true ∧ spec.Covered ∧
    (spec.Assumed → ∀ ctx, spec.Contexts ctx → ∃ c, src.checked = .ok c ∧
      CertifiedAt (src.semAt ctx) c ctx (runtimeCode bytes) (spec.Valid ctx) (spec.Allowed ctx)
        (spec.Post ctx) (spec.gas ctx))

/-! ## Bytes -/

theorem runtimeCode_toNat (code : ByteArray) :
    runtimeCode (code.data.toList.map (·.toNat)) = code := by
  cases code with
  | mk data =>
    simp only [runtimeCode, List.map_map]
    congr
    simp [Function.comp_def, UInt8.ofNat_toNat]

theorem all_lt_toNat (code : ByteArray) :
    (code.data.toList.map (·.toNat)).all (· < 256) = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq]
  intro b _
  exact b.toNat_lt

/-- A proof about `code` is about `bytes` once the kernel has checked that `code`'s bytes are
`bytes` (the binding of the fresh export to the fresh compile). -/
theorem runtimeCode_eq {code : ByteArray} {bytes : List Nat}
    (h : code.data.toList.map (·.toNat) = bytes) : runtimeCode bytes = code := by
  rw [← h]; exact runtimeCode_toNat code

theorem all_lt_of_eq {code : ByteArray} {bytes : List Nat}
    (h : code.data.toList.map (·.toNat) = bytes) : bytes.all (· < 256) = true := by
  rw [← h]; exact all_lt_toNat code

/-! ## What the expected theorem says of the bytes -/

theorem CertifiedAt.terminates {S : Sem} {p : S.Prog} {ctx : Context} {code : ByteArray}
    {Valid : Call → Prop} {Allowed Post : Call → Observable → Prop} {G : Call → Nat}
    (h : CertifiedAt S p ctx code Valid Allowed Post G) : Terminates S p Valid Allowed :=
  fun call hc => by
    obtain ⟨obs, hs, -⟩ := h.translation.terminates call hc
    exact ⟨obs, hs, h.spec.allowed call hc obs hs⟩

/-- **Total correctness of the exact bytes in a covered context**, from the gas bound on: the
bytes' observable is the source's, allowed and meeting the specification. -/
theorem Expected.bytecode_total {ws : List Nat} {src : Source ws} {spec : Spec} {bytes : List Nat}
    (h : Expected src spec bytes) (ha : spec.Assumed) {ctx : Context} (hctx : spec.Contexts ctx)
    (call : Call) (hc : spec.Valid ctx call) :
    spec.gas ctx call < 2 ^ 64 ∧ ∀ gas, spec.gas ctx call ≤ gas → gas < 2 ^ 256 → ∃ obs,
      runAt ctx gas (runtimeCode bytes) call = some obs ∧
        spec.Allowed ctx call obs ∧ spec.Post ctx call obs := by
  obtain ⟨c, -, hcert⟩ := h.2.2 ha ctx hctx
  obtain ⟨hG, hr⟩ := hcert.translation.resources call hc
  refine ⟨hG, fun gas h1 h2 => ?_⟩
  obtain ⟨obs, hs, hal⟩ := hcert.terminates call hc
  exact ⟨obs, (hr gas h1 h2).trans hs, hal, hcert.spec.meets call hc obs hs⟩

/-- **Partial correctness of the exact bytes at every gas in a covered context**: an allowed
result meeting the specification, or a failure that changes nothing. -/
theorem Expected.bytecode_any {ws : List Nat} {src : Source ws} {spec : Spec} {bytes : List Nat}
    (h : Expected src spec bytes) (ha : spec.Assumed) {ctx : Context} (hctx : spec.Contexts ctx)
    (gas : Nat) (hg : gas < 2 ^ 256) (call : Call) (hc : spec.Valid ctx call) (obs : Observable)
    (hrun : runAt ctx gas (runtimeCode bytes) call = some obs) :
    (spec.Allowed ctx call obs ∧ spec.Post ctx call obs) ∨ Inert call obs := by
  obtain ⟨c, -, hcert⟩ := h.2.2 ha ctx hctx
  rcases hcert.translation.equiv gas hg call hc obs hrun with e | e
  · obtain ⟨obs', hs, ha'⟩ := hcert.terminates call hc
    obtain rfl : obs' = obs := Option.some.inj (hs.symm.trans e)
    exact Or.inl ⟨ha', hcert.spec.meets call hc obs' hs⟩
  · exact Or.inr e

/-! ## Negative controls: no expected theorem is free -/

theorem not_expected_of_vacuous_post {ws : List Nat} {src : Source ws} {spec : Spec} {bytes : List Nat}
    (h : ∀ ctx call obs, spec.Valid ctx call → spec.Post ctx call obs) :
    ¬ Expected src spec bytes :=
  fun ⟨_, ⟨_, _, _, ⟨ctx, call, obs, _, hv, hn⟩, _⟩, _⟩ => hn (h ctx call obs hv)

theorem not_expected_of_vacuous_allowed {ws : List Nat} {src : Source ws} {spec : Spec} {bytes : List Nat}
    (h : ∀ ctx call obs, spec.Valid ctx call → spec.Allowed ctx call obs) :
    ¬ Expected src spec bytes :=
  fun ⟨_, ⟨_, _, _, _, ⟨ctx, call, obs, _, hv, _, hn⟩⟩, _⟩ => hn (h ctx call obs hv)

theorem not_expected_of_uncovered {ws : List Nat} {src : Source ws} {spec : Spec} {bytes : List Nat}
    (h : ∀ ctx, ¬ spec.Contexts ctx) : ¬ Expected src spec bytes :=
  fun ⟨_, ⟨⟨ctx, hc⟩, _⟩, _⟩ => h ctx hc

theorem not_expected_of_dead_entry {ws : List Nat} {src : Source ws} {spec : Spec} {bytes : List Nat}
    {ctx : Context} (hctx : spec.Contexts ctx) {e : String × (Context → Call → Prop)}
    (he : e ∈ spec.entries) (hdead : ∀ call, spec.Valid ctx call → ¬ e.2 ctx call) :
    ¬ Expected src spec bytes :=
  fun ⟨_, ⟨_, _, hent, _⟩, _⟩ => by
    obtain ⟨call, hv, he'⟩ := hent ctx hctx e he
    exact hdead call hv he'

theorem not_expected_of_check_error {ws : List Nat} {src : Source ws} {spec : Spec} {bytes : List Nat}
    {e : TypeCheck.TypeError} (ha : spec.Assumed) {ctx : Context} (hctx : spec.Contexts ctx)
    (h : src.checked = .error e) : ¬ Expected src spec bytes :=
  fun ⟨_, _, hx⟩ => by
    obtain ⟨c, hc, -⟩ := hx ha ctx hctx
    rw [h] at hc; cases hc

/-! ## The default context is `Shapes`' single frame -/

theorem runAt_default : runAt Context.default = Final.Target.runWith := by
  funext gas code call
  simp only [runAt, Context.default]
  rw [Final.Target.runWithFrom_callerAddress]

/-- An existing `Shapes.Certified` statement is `CertifiedAt` the default context. -/
theorem certifiedAt_default {fuel : Nat} {c : TypeCheck.CheckedContract} {code : ByteArray}
    {Valid : Call → Prop} {Allowed Post : Call → Observable → Prop} {G : Call → Nat}
    (h : Certified (solidCore fuel) c code Valid Allowed Post G) :
    CertifiedAt (solidCoreFrom Context.default.caller fuel) c Context.default code Valid Allowed
      Post G where
  translation :=
    { inhabited := h.inhabited
      equiv := by
        intro gas hg call hc obs hrun
        rw [runAt_default] at hrun
        exact h.equiv gas hg call hc obs hrun
      terminates := fun call hc => by
        obtain ⟨obs, hs, -⟩ := h.terminates call hc
        exact ⟨obs, hs, trivial⟩
      resources := fun call hc => by
        obtain ⟨hG, hr⟩ := h.resources call hc
        exact ⟨hG, fun gas h1 h2 => by rw [runAt_default]; exact hr gas h1 h2⟩ }
  spec :=
    { allowed := fun call hc obs hs => by
        obtain ⟨obs', hs', ha⟩ := h.terminates call hc
        have e : (solidCore fuel).run c call = some obs := hs
        rw [e] at hs'; cases hs'; exact ha
      meets := h.meets }

/-- info: 'SolidCore.Verify.Generic.Expected.bytecode_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Expected.bytecode_total

end SolidCore.Verify.Generic
