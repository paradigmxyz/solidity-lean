import SolidCore.Spec.TrustedBase
import EvmInteraction.Simulation.Interaction
import SolidCore.Solidity.Ast

/-!
# solar-verify's trusted base, item by item, as precise hypotheses

`SolidCore.Spec.TrustedBase.Assumptions` names each item of solar-verify's trusted base
(crates/verify/README.md, "Trusted base") as a field, but leaves each field an arbitrary
proposition. This module gives each item a precise statement over the objects the composition
already has: `SolarTV.Call`/`Observable` and a `Sem`, the transcripts of query/answer exchanges
SolidCore's interaction trees make with the outside world (`EvmCompiler.Simulation.Interaction`),
the core language of ghost code (`SolidCore.Spec.Ghost`) and the Solidity AST. `Hyps` collects
them, `Hyps.toAssumptions` instantiates `Assumptions` with them, and `spec_of_verdict_hyps` is
`spec_of_verdict` with the precise hypotheses.

For each item: the statement, a witness that it is satisfiable (not `False` in disguise), where
it is cheap a witness that it is not trivially `True` either, and the discharge for code that does
not use the feature.

| README item | Here | Discharged when |
|---|---|---|
| keccak256 injective, results in `[2^128, 2^256)` | `KeccakSeparated` of the call's preimages | no preimages (`keccakSeparated_empty`); checked by the kernel on concrete ones (`keccakSeparated_mapping`) |
| `@custom:assume` | `AssumesHold` | the body has no assume (`assumesHold_of_noAssume`) |
| `@custom:trusted` (internal) | `MeetsContract` | no trusted function |
| `@custom:trusted` (external) | `TrustedHold` | no trusted function (`trustedHold_nil`), or the spec proved (`trustedHold_of_holds`) |
| interface ensures | `InterfaceEnsures` | every external call fails, e.g. SolidCore's fail-open answers (`DefaultCalls`) |
| no delegatecall into the contract | `NoForeignWrites` within a call, `Reach` across calls | `DefaultCalls` |
| assembly slots disjoint, memory-safe | `AsmFree` (stronger) | the source has no assembly (`AsmFree` by `decide`) |
| `Math.mulDiv` summary | `MulDivSummary` | no `Math.mulDiv` |
| view calls deterministic | `ViewDeterministic` | `DefaultCalls` |

Two items are stated against data the theorem's user supplies rather than derived from SolidCore's
run, and the gap is named where they are: the keccak256 preimages a call hashes
(`Hyps.keccakInputs`) and the transcript of a call (`Hyps.transcript`; `transcriptWith` computes it
from an interaction tree and an answerer, but `Source.run` does not yet expose its tree). Item 1
(the parser, the VC encoding and the solvers) stays `Verdict` itself.
-/

namespace SolidCore.Spec.TrustedBase

open SolarTV SolidCore.Spec

/-! ## keccak256 -/

/-- A set of keccak256 preimages (byte lists), as a predicate. -/
abbrev Preimages := List Nat → Prop

/-- **keccak256 is separated on `S`**: injective on `S`, and every image at least `2 ^ 128`, so
no image is a small constant slot. Stated for every input it is false (`not_keccakSeparated_univ`);
solar-verify's encoding uses it only on the preimages a call hashes. -/
def KeccakSeparated (S : Preimages) : Prop :=
  (∀ x y, S x → S y → keccakWord x = keccakWord y → x = y) ∧ ∀ x, S x → 2 ^ 128 ≤ keccakWord x

theorem KeccakSeparated.mono {S T : Preimages} (h : KeccakSeparated T) (hST : ∀ x, S x → T x) :
    KeccakSeparated S :=
  ⟨fun x y hx hy he => h.1 x y (hST x hx) (hST y hy) he, fun x hx => h.2 x (hST x hx)⟩

/-- A call that hashes nothing needs nothing of keccak256. -/
theorem keccakSeparated_empty : KeccakSeparated (fun _ => False) :=
  ⟨fun _ _ h => h.elim, fun _ h => h.elim⟩

/-- Injectivity on a list from distinct images. -/
theorem inj_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, _, hx, _, _, _ => by simp at hx
  | a :: l, h, x, hx, y, hy, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd ⟨y, hy, he.symm⟩ h.1
    · exact absurd ⟨x, hx, he⟩ h.1
    · exact inj_of_nodup_map h.2 x hx y hy he

/-- Separation on a list, from its images: distinct and each at least `2 ^ 128`. -/
theorem keccakSeparated_of_images {L : List (List Nat)} {H : List Nat}
    (hH : L.map keccakWord = H) (hnd : H.Nodup) (hge : ∀ v ∈ H, 2 ^ 128 ≤ v) :
    KeccakSeparated (· ∈ L) :=
  ⟨fun x y hx hy he => inj_of_nodup_map (hH ▸ hnd) x hx y hy he,
    fun _ hx => hge _ (hH ▸ List.mem_map_of_mem hx)⟩

/-- The preimage of the slot of `m[k]` for a mapping `m` at slot `s`: `k` then `s`, as words. -/
def mappingPreimage (k s : Nat) : List Nat := wordBytes k ++ wordBytes s

/-- The slots of `m[0]`, `m[1]` and `m[0x2000]` (`msg.sender` for `callerAddress`) for mappings at slots 0
and 1. -/
def mappingPreimages : List (List Nat) :=
  [mappingPreimage 0 0, mappingPreimage 1 0, mappingPreimage 0x2000 0, mappingPreimage 0 1,
    mappingPreimage 1 1, mappingPreimage 0x2000 1]

/-! Their keccak256 images, each by the kernel's evaluation of the sponge (one per declaration,
so that the kernel's caches stay small). -/

set_option maxRecDepth 100000 in
theorem image0 : keccakWord (mappingPreimage 0 0) =
    0xad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem image1 : keccakWord (mappingPreimage 1 0) =
    0xada5013122d395ba3c54772283fb069b10426056ef8ca54750cb9bb552a59e7d := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem image2 : keccakWord (mappingPreimage 0x2000 0) =
    0x7a590e257d634ba5db8688524231d50b5351ea3cd1a840d196ed0e2098593fd8 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem image3 : keccakWord (mappingPreimage 0 1) =
    0xa6eef7e35abe7026729641147f7915573c7e97b47efa546f5f6e3230263bcb49 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem image4 : keccakWord (mappingPreimage 1 1) =
    0xcc69885fda6bcc1a4ace058b4a62bf5e179ea78fd58a1ccd71c22cc9b688792f := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem image5 : keccakWord (mappingPreimage 0x2000 1) =
    0x38da9dc9759c46bd12ce677a753bb966a85f8995667f5aade8c3f5d0f1de587a := by
  decide +kernel

theorem mappingPreimages_images :
    mappingPreimages.map keccakWord =
      [0xad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5,
       0xada5013122d395ba3c54772283fb069b10426056ef8ca54750cb9bb552a59e7d,
       0x7a590e257d634ba5db8688524231d50b5351ea3cd1a840d196ed0e2098593fd8,
       0xa6eef7e35abe7026729641147f7915573c7e97b47efa546f5f6e3230263bcb49,
       0xcc69885fda6bcc1a4ace058b4a62bf5e179ea78fd58a1ccd71c22cc9b688792f,
       0x38da9dc9759c46bd12ce677a753bb966a85f8995667f5aade8c3f5d0f1de587a] := by
  simp only [mappingPreimages, List.map_cons, List.map_nil, image0, image1, image2, image3, image4,
    image5]

/-- **Satisfiable on real preimages**: keccak256 is separated on `mappingPreimages`. -/
theorem keccakSeparated_mapping : KeccakSeparated (· ∈ mappingPreimages) :=
  keccakSeparated_of_images mappingPreimages_images (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem not_keccakSeparated_univ : ¬ KeccakSeparated (fun _ => True) := by
  intro h
  have := h.1 [0] [256] trivial trivial (by decide +kernel)
  simp at this

/-! ## `@custom:assume` and `@custom:trusted`, on the core language of ghost code -/

namespace Core
open SolidCore.Spec.Ghost

/-- The program with every `assume` replaced by `skip`. -/
def dropAssumes : Ghost.Stmt → Ghost.Stmt
  | .assume _ => .skip
  | .seq s t => .seq (dropAssumes s) (dropAssumes t)
  | .ite c s t => .ite c (dropAssumes s) (dropAssumes t)
  | .loop c b => .loop c (dropAssumes b)
  | s => s

/-- The program has no `assume`. -/
def noAssume : Ghost.Stmt → Bool
  | .assume _ => false
  | .seq s t => noAssume s && noAssume t
  | .ite _ s t => noAssume s && noAssume t
  | .loop _ b => noAssume b
  | _ => true

/-- **Every `@custom:assume` holds where it is reached** from `σ`: every execution of the program
without its assumes is one of the program, so no assume cuts an execution off. -/
def AssumesHold (s : Ghost.Stmt) (σ : Store) : Prop :=
  ∀ o, Exec (dropAssumes s) σ o → Exec s σ o

/-- Dropping assumes only adds executions. -/
theorem exec_dropAssumes {s : Ghost.Stmt} {σ : Store} {o : Out} (h : Exec s σ o) :
    Exec (dropAssumes s) σ o := by
  induction h with
  | skip => exact .skip
  | assign => exact .assign
  | requireOk h => exact .requireOk h
  | requireRev h => exact .requireRev h
  | seqOk _ _ ih1 ih2 => exact .seqOk ih1 ih2
  | seqRev _ ih => exact .seqRev ih
  | seqFail _ ih => exact .seqFail ih
  | iteT hc _ ih => exact .iteT hc ih
  | iteF hc _ ih => exact .iteF hc ih
  | loopDone hc => exact .loopDone hc
  | loopOk hc _ _ ih1 ih2 => exact .loopOk hc ih1 ih2
  | loopRev hc _ ih => exact .loopRev hc ih
  | loopFail hc _ ih => exact .loopFail hc ih
  | ghost => exact .ghost
  | assertOk h => exact .assertOk h
  | assertFail h => exact .assertFail h
  | assume _ => exact .skip

theorem dropAssumes_of_noAssume : ∀ {s : Ghost.Stmt}, noAssume s = true → dropAssumes s = s
  | .skip, _ | .assign _ _, _ | .require _, _ | .ghost _ _, _ | .assert _, _ => rfl
  | .assume _, h => by simp [noAssume] at h
  | .seq s t, h => by
    simp only [noAssume, Bool.and_eq_true] at h
    simp [dropAssumes, dropAssumes_of_noAssume h.1, dropAssumes_of_noAssume h.2]
  | .ite c s t, h => by
    simp only [noAssume, Bool.and_eq_true] at h
    simp [dropAssumes, dropAssumes_of_noAssume h.1, dropAssumes_of_noAssume h.2]
  | .loop c b, h => by
    simp only [noAssume] at h
    simp [dropAssumes, dropAssumes_of_noAssume h]

/-- **Discharged without assumes.** -/
theorem assumesHold_of_noAssume {s : Ghost.Stmt} (h : noAssume s = true) (σ : Store) :
    AssumesHold s σ := by
  intro o ho
  rwa [dropAssumes_of_noAssume h] at ho

/-- What a proof of `s` gives the program without its assumes, where they hold. -/
theorem spec_of_assumes {s : Ghost.Stmt} {σ : Store} {Q : Out → Prop}
    (hs : ∀ o, Exec s σ o → Q o) (ha : AssumesHold s σ) : ∀ o, Exec (dropAssumes s) σ o → Q o :=
  fun o ho => hs o (ha o ho)

/-- `@custom:assume x`. -/
def assumeX : Ghost.Stmt := .assume (.var "x")

/-- **Satisfiable**: `assume x` holds from a store where `x = 1`. -/
theorem assumesHold_assumeX : AssumesHold assumeX (fun _ => 1) := by
  intro o ho
  cases ho
  exact .assume (by simp [Exp.eval])

/-- **Not trivial**: it fails from a store where `x = 0`. -/
theorem not_assumesHold_assumeX : ¬ AssumesHold assumeX (fun _ => 0) := by
  intro h
  have := h _ (Exec.skip (σ := fun _ => 0))
  cases this with
  | assume hx => exact hx (by simp [Exp.eval])

/-- **A `@custom:trusted` internal function meets its contract**: from every store meeting `req`,
every execution of its body `s` meets `ens`. -/
def MeetsContract (s : Ghost.Stmt) (req : Store → Prop) (ens : Store → Out → Prop) : Prop :=
  ∀ σ, req σ → ∀ o, Exec s σ o → ens σ o

/-- **Satisfiable**: `r = 1` ensures `r == 1`. -/
theorem meetsContract_assign :
    MeetsContract (.assign "r" (.lit 1)) (fun _ => True)
      (fun _ o => ∃ σ', o = .ok σ' ∧ σ' "r" = 1) := by
  intro σ _ o ho
  cases ho
  exact ⟨_, rfl, by simp [Store.set, Exp.eval]⟩

/-- **Not trivial**: `r = 0` does not. -/
theorem not_meetsContract_assign :
    ¬ MeetsContract (.assign "r" (.lit 0)) (fun _ => True)
      (fun _ o => ∃ σ', o = .ok σ' ∧ σ' "r" = 1) := by
  intro h
  obtain ⟨σ', h1, h2⟩ := h (fun _ => 0) trivial _ .assign
  cases h1
  simp [Store.set, Exp.eval] at h2

end Core

/-! ## `@custom:trusted` external and public functions, on calls -/

/-- The bundle restricted to the functions named. -/
def Bundle.only (b : Bundle) (names : List String) : Bundle :=
  { b with spec := { b.spec with specs := b.spec.specs.filter (fun fs => names.contains fs.name) } }

/-- **The `@custom:trusted` external functions `names` meet their specs** on `p` in `S`: their
bodies are not verified, so their specs are assumed. -/
def TrustedHold (S : Sem) (p : S.Prog) (scope : Call → Prop) (b : Bundle) (ctxOf : Call → Ctx)
    (step : GhostStep) (names : List String) : Prop :=
  Holds S p scope (Bundle.only b names) ctxOf step

/-- **Discharged without trusted functions.** -/
theorem trustedHold_nil {S : Sem} {p : S.Prog} {scope : Call → Prop} {b : Bundle}
    {ctxOf : Call → Ctx} {step : GhostStep} : TrustedHold S p scope b ctxOf step [] := by
  intro fs hfs
  simp [Bundle.only] at hfs

/-- **Discharged by a proof**: a spec proved of every function, in Lean or otherwise, holds of the
trusted ones. -/
theorem trustedHold_of_holds {S : Sem} {p : S.Prog} {scope : Call → Prop} {b : Bundle}
    {ctxOf : Call → Ctx} {step : GhostStep} (names : List String)
    (h : Holds S p scope b ctxOf step) : TrustedHold S p scope b ctxOf step names := by
  intro fs hfs
  simp only [Bundle.only, List.mem_filter] at hfs
  exact h fs hfs.1

/-! ## External calls: interface ensures, view calls and writes by others

SolidCore runs a function as an interaction tree whose external calls are `Query.external` nodes,
answered by an answerer; a run's transcript is the list of its exchanges. These items are
properties of a transcript's call exchanges: the world the call was made in, the request and the
response (whose `postWorld` the caller adopts).
-/

open EvmCompiler.Simulation

/-- The call exchanges of a transcript: world, request, response. -/
def callsOf : Interaction.Transcript → List (OpenWorld × CallRequest × CallResponse)
  | [] => []
  | ⟨.external w (.call r), a⟩ :: tr => (w, r, a) :: callsOf tr
  | _ :: tr => callsOf tr

/-- The transcript of an interaction tree answered by `ans`. -/
def transcriptWith {ε α : Type} (ans : (q : Query) → Answer q) :
    Interaction ε α → Interaction.Transcript
  | .done _ => []
  | .request q k => ⟨q, ans q⟩ :: transcriptWith ans (k (ans q))

/-- The transcript is a branch of the tree. -/
theorem follows_transcriptWith {ε α : Type} (ans : (q : Query) → Answer q) :
    ∀ t : Interaction ε α, Interaction.Follows t (transcriptWith ans t)
  | .done _ => .nil _
  | .request q k => .request (follows_transcriptWith ans (k (ans q)))

/-- **Interface ensures**: every external call that returns meets `ens`, the interface's ensures
on the request (target and calldata) and the returned data. -/
def InterfaceEnsures (ens : CallRequest → CallResponse → Prop) (tr : Interaction.Transcript) :
    Prop :=
  ∀ c ∈ callsOf tr, c.2.2.success = true → ens c.2.1 c.2.2

/-- What a view call may read, as solar-verify's README puts it: the balance and code of every
account, and the storage of the calling contract `self`. -/
def ReadAgree (self : InteractionAddress) (w w' : OpenWorld) : Prop :=
  (∀ a, (w.accounts.find? a).map (fun acc => (acc.balance, acc.codeBytes)) =
    (w'.accounts.find? a).map (fun acc => (acc.balance, acc.codeBytes))) ∧
  ∀ k, (w.accounts.find? self).map (fun acc => acc.storage.find? k) =
    (w'.accounts.find? self).map (fun acc => acc.storage.find? k)

/-- **View calls are deterministic**: two static calls to the same target with the same calldata,
from worlds that agree on what a view call may read, answer alike, whatever gas each carried. -/
def ViewDeterministic (self : InteractionAddress) (tr : Interaction.Transcript) : Prop :=
  ∀ c₁ ∈ callsOf tr, ∀ c₂ ∈ callsOf tr, c₁.2.1.kind = .staticcall → c₂.2.1.kind = .staticcall →
    c₁.2.1.recipient = c₂.2.1.recipient → c₁.2.1.calldata = c₂.2.1.calldata →
    ReadAgree self c₁.1 c₂.1 →
    c₁.2.2.success = c₂.2.2.success ∧ c₁.2.2.returnData = c₂.2.2.returnData

/-- `self`'s storage in a world, as a slot function (absent slots and accounts read zero). -/
def selfSlots (self : InteractionAddress) (w : OpenWorld) : Nat → Nat := fun k =>
  (((w.accounts.find? self).bind fun acc => acc.storage.find? (EvmYul.UInt256.ofNat k)).map
    EvmYul.UInt256.toNat).getD 0

/-- Storage `σ'` is reachable from `σ` through the contract's own functions: by successful calls of
`p` in `S`, each from the storage the previous one left. -/
inductive Reach (S : Sem) (p : S.Prog) : (Nat → Nat) → (Nat → Nat) → Prop
  | refl (σ : Nat → Nat) : Reach S p σ σ
  | step {σ σ' : Nat → Nat} (call : Call) (obs : Observable) :
      slotValue call.storage = σ → S.run p call = some obs → obs.success = true →
      Reach S p obs.storage σ' → Reach S p σ σ'

theorem Reach.trans {S : Sem} {p : S.Prog} {σ σ' σ'' : Nat → Nat} (h : Reach S p σ σ')
    (h' : Reach S p σ' σ'') : Reach S p σ σ'' := by
  induction h with
  | refl => exact h'
  | step call obs hs hr hok _ ih => exact .step call obs hs hr hok (ih h')

/-- **No delegatecall into the contract**, within a call: across each external call, `self`'s
storage changes only by reentrant calls of its own functions. Across transactions the same
relation, `Reach S p deployed (slotValue call.storage)`, restricts the calls a theorem covers to
those from a storage the contract's functions reach from deployment (`Hyps.reachable`). -/
def NoForeignWrites (S : Sem) (p : S.Prog) (self : InteractionAddress)
    (tr : Interaction.Transcript) : Prop :=
  ∀ c ∈ callsOf tr, Reach S p (selfSlots self c.1) (selfSlots self c.2.2.postWorld)

/-- The default, fail-open response to a call from `w`: failure, no data, the world unchanged. -/
def defaultResponse (w : OpenWorld) : CallResponse :=
  CallResponse.mk false default w (EvmYul.UInt256.ofNat 0)

/-- Every external call of the transcript got the default, fail-open answer: failure, no data,
the world unchanged. SolidCore's `contextAnswer` gives it to every call that is not a precompile's. -/
def DefaultCalls (tr : Interaction.Transcript) : Prop :=
  ∀ c ∈ callsOf tr, c.2.2 = defaultResponse c.1

/-- An answerer that gives every external call the default answer. -/
def DefaultOnCalls (ans : (q : Query) → Answer q) : Prop :=
  ∀ w r, ans (.external w (.call r)) = Query.defaultAnswer (.external w (.call r))

theorem defaultCalls_cons_call {w : OpenWorld} {r : CallRequest} {a : CallResponse}
    {tr : Interaction.Transcript}
    (ha : a = defaultResponse w) (h : DefaultCalls tr) :
    DefaultCalls (⟨.external w (.call r), a⟩ :: tr) := by
  intro c hc
  simp only [callsOf, List.mem_cons] at hc
  rcases hc with rfl | hc
  · exact ha
  · exact h c hc

/-- An answerer defaulting on calls yields a transcript with default calls, on every tree. -/
theorem defaultCalls_transcriptWith {ε α : Type} {ans : (q : Query) → Answer q}
    (hans : DefaultOnCalls ans) : ∀ t : Interaction ε α, DefaultCalls (transcriptWith ans t)
  | .done _ => fun _ h => by simp [transcriptWith, callsOf] at h
  | .request q k => by
    have ih := defaultCalls_transcriptWith hans (k (ans q))
    match q with
    | .external w (.call r) =>
      exact defaultCalls_cons_call ((hans w r).trans rfl) ih
    | .external w (.create r) =>
      intro c hc
      exact ih c (by simpa [transcriptWith, callsOf] using hc)
    | .resource r =>
      intro c hc
      exact ih c (by simpa [transcriptWith, callsOf] using hc)

/-- **Interface ensures, discharged** where no external call returns. -/
theorem interfaceEnsures_of_default {ens : CallRequest → CallResponse → Prop}
    {tr : Interaction.Transcript} (h : DefaultCalls tr) : InterfaceEnsures ens tr := by
  intro c hc hs
  rw [h c hc] at hs
  cases hs

/-- **View calls, discharged** where every call gets the default answer. -/
theorem viewDeterministic_of_default {self : InteractionAddress} {tr : Interaction.Transcript}
    (h : DefaultCalls tr) : ViewDeterministic self tr := by
  intro c₁ h₁ c₂ h₂ _ _ _ _ _
  rw [h c₁ h₁, h c₂ h₂]
  exact ⟨rfl, rfl⟩

/-- **Writes by others, discharged** where every call gets the default answer. -/
theorem noForeignWrites_of_default {S : Sem} {p : S.Prog} {self : InteractionAddress}
    {tr : Interaction.Transcript} (h : DefaultCalls tr) : NoForeignWrites S p self tr := by
  intro c hc
  rw [h c hc]
  exact .refl _

/-- A static call to target 1 with empty calldata, from the default world. -/
def staticReq : CallRequest :=
  { kind := .staticcall, requestedGas := EvmYul.UInt256.ofNat 0, caller := default,
    recipient := default, codeAddress := default, transferValue := EvmYul.UInt256.ofNat 0,
    apparentValue := EvmYul.UInt256.ofNat 0, calldata := .empty, permission := false }

/-- The same static call, answered with `ok` and the data `d`. -/
def staticEx (ok : Bool) (d : ByteArray) : Interaction.Exchange :=
  ⟨.external default (.call staticReq),
    (CallResponse.mk ok d default (EvmYul.UInt256.ofNat 0) : CallResponse)⟩

/-- **Satisfiable with calls that return**: the same view call twice, answered alike. -/
theorem viewDeterministic_twice (self : InteractionAddress) (d : ByteArray) :
    ViewDeterministic self [staticEx true d, staticEx true d] := by
  intro c₁ h₁ c₂ h₂ _ _ _ _ _
  simp only [callsOf, staticEx, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem readAgree_refl (self : InteractionAddress) (w : OpenWorld) : ReadAgree self w w :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- **Not trivial**: the same view call answered once with success and once without breaks it. -/
theorem not_viewDeterministic (self : InteractionAddress) :
    ¬ ViewDeterministic self [staticEx true .empty, staticEx false .empty] := by
  intro h
  have := h (default, staticReq, CallResponse.mk true .empty default (EvmYul.UInt256.ofNat 0))
    (by simp [callsOf, staticEx]) (default, staticReq, CallResponse.mk false .empty default
      (EvmYul.UInt256.ofNat 0)) (by simp [callsOf, staticEx]) rfl rfl rfl rfl (readAgree_refl _ _)
  simp at this

/-! ## Inline assembly -/

open SolidCore.Solidity in
mutual
/-- The statement contains inline assembly. -/
def stmtHasAsm : Solidity.Stmt → Bool
  | .inlineAssembly _ => true
  | .block ss => stmtsHaveAsm ss
  | .ifElse _ s none => stmtHasAsm s
  | .ifElse _ s (some t) => stmtHasAsm s || stmtHasAsm t
  | .whileLoop _ s => stmtHasAsm s
  | .doWhile s _ => stmtHasAsm s
  | .forLoop none _ _ s => stmtHasAsm s
  | .forLoop (some i) _ _ s => stmtHasAsm i || stmtHasAsm s
  | .tryCatch _ cs => clausesHaveAsm cs
  | .tryCatchReturns _ _ s cs => stmtHasAsm s || clausesHaveAsm cs
  | .unchecked s => stmtHasAsm s
  | .empty | .varDecl _ _ | .expr _ | .emitEvent _ | .revertCall _ | .returnValues _ | .break
  | .continue | .modifierPlaceholder => false

def stmtsHaveAsm : List Solidity.Stmt → Bool
  | [] => false
  | s :: ss => stmtHasAsm s || stmtsHaveAsm ss

def clausesHaveAsm : List Solidity.CatchClause → Bool
  | [] => false
  | .clause _ _ s :: cs => stmtHasAsm s || clausesHaveAsm cs
end

/-- A body that may be absent contains inline assembly. -/
def bodyHasAsm : Option Solidity.Stmt → Bool
  | none => false
  | some s => stmtHasAsm s

/-- A contract item contains inline assembly. -/
def itemHasAsm : Solidity.ContractItem → Bool
  | .function f => bodyHasAsm f.body
  | .modifierDecl m => bodyHasAsm m.body
  | _ => false

/-- A source item contains inline assembly. -/
def sourceItemHasAsm : Solidity.SourceItem → Bool
  | .contract c => c.items.any itemHasAsm
  | .freeFunction f => bodyHasAsm f.body
  | _ => false

/-- **No inline assembly** anywhere in the source unit. SolidCore's type checker rejects inline
assembly, and its AST keeps a block as an unparsed string, so the composition can rely only on
this, which is stronger than README item 5 (raw slots that assembly reaches are disjoint from the
declared variables, and assembly is memory-safe) and implies it: with no assembly there is no
raw slot and no assembly memory access. Contracts with assembly fail closed, at type checking. -/
def AsmFree (u : Solidity.SourceUnit) : Prop := u.items.any sourceItemHasAsm = false

instance (u : Solidity.SourceUnit) : Decidable (AsmFree u) := by unfold AsmFree; infer_instance

/-- A source unit with one contract and one function with body `body`. -/
def exampleFn (body : Solidity.Stmt) : Solidity.SourceUnit :=
  Solidity.SourceUnit.mk [.contract (Solidity.ContractDecl.mk .contract "C" false none []
    [.function { body := some body }])]

/-- **Satisfiable**: a contract with one empty function. -/
theorem asmFree_example : AsmFree (exampleFn .empty) := by decide

/-- **Not trivial**: a function whose body is an assembly block. -/
theorem not_asmFree_example :
    ¬ AsmFree (exampleFn (.block [.inlineAssembly "sstore(0, 1)"])) := by
  decide

/-! ## `Math.mulDiv` -/

/-- OpenZeppelin's `Math.mulDiv(x, y, d)` on words: `⌊x * y / d⌋`, or a revert (`none`) when `d` is
zero or the quotient does not fit a word. -/
def ozMulDiv (x y d : Nat) : Option Nat :=
  if d = 0 ∨ 2 ^ 256 ≤ x * y / d then none else some (x * y / d)

/-- **`Math.mulDiv` is OpenZeppelin's**: the library function, as a function of its word arguments
to its result or a revert (`impl`), agrees with `ozMulDiv` on every word. -/
def MulDivSummary (impl : Nat → Nat → Nat → Option Nat) : Prop :=
  ∀ x y d, x < 2 ^ 256 → y < 2 ^ 256 → d < 2 ^ 256 → impl x y d = ozMulDiv x y d

/-- **Satisfiable**: by the summary itself. -/
theorem mulDivSummary_oz : MulDivSummary ozMulDiv := fun _ _ _ _ _ _ => rfl

/-- **Not trivial**: plain `x * y / d` without the overflow check is not the summary
(`2^255 * 4 / 2` overflows a word). -/
theorem not_mulDivSummary_unchecked :
    ¬ MulDivSummary (fun x y d => if d = 0 then none else some (x * y / d)) := by
  intro h
  have := h (2 ^ 255) 4 2 (by decide) (by decide) (by decide)
  simp [ozMulDiv] at this

/-- The summary's full-precision meaning: what it returns is the floor of the exact quotient. -/
theorem ozMulDiv_spec {x y d r : Nat} (h : ozMulDiv x y d = some r) :
    0 < d ∧ r * d ≤ x * y ∧ x * y < (r + 1) * d ∧ r < 2 ^ 256 := by
  unfold ozMulDiv at h
  split at h
  · cases h
  · rename_i hn
    cases h
    have hd : 0 < d := Nat.pos_of_ne_zero (fun h0 => hn (Or.inl h0))
    refine ⟨hd, Nat.div_mul_le_self _ _, ?_, Nat.lt_of_not_le (fun h' => hn (Or.inr h'))⟩
    rw [Nat.mul_comm _ d]
    exact Nat.lt_mul_div_succ _ hd

/-! ## All of it -/

/-- The data the precise trusted base is stated over, for a source program `p` in `S`:

* `keccakInputs call`: the keccak256 preimages the call hashes. Supplied, not derived: SolidCore
  hashes inside its interpreter, not through a query, so its runs do not yet expose them.
* `transcript call`: the call's exchanges with the outside world. Supplied: `transcriptWith`
  computes it from an interaction tree and an answerer, but `Source.run` does not expose its tree.
* `self`: the contract's address in those worlds; `deployed`: its storage after deployment.
* `ifaceEns`: the external interfaces' ensures, on a request and its response.
* `assumeSites call`: each body with `@custom:assume`s the call runs, with the store it starts
  from; `trustedBodies`: each `@custom:trusted` internal function's body, requires and ensures;
  `trustedNames`: the `@custom:trusted` external functions.
* `source`: the Solidity source unit SolidCore checked; `mulDiv`: the contract's `Math.mulDiv`,
  if it has one. -/
structure Hyps (S : Sem) (p : S.Prog) where
  keccakInputs : Call → Preimages
  transcript : Call → Interaction.Transcript
  self : InteractionAddress
  deployed : Nat → Nat
  ifaceEns : CallRequest → CallResponse → Prop
  assumeSites : Call → List (Ghost.Stmt × Ghost.Store)
  trustedBodies : List (Ghost.Stmt × (Ghost.Store → Prop) × (Ghost.Store → Ghost.Out → Prop))
  trustedNames : List String
  source : Solidity.SourceUnit
  mulDiv : Option (Nat → Nat → Nat → Option Nat)

namespace Hyps

variable {S : Sem} {p : S.Prog} (H : Hyps S p)

/-- The contract's `Math.mulDiv` is OpenZeppelin's, if it has one. -/
def MulDivOk : Prop := ∀ f, H.mulDiv = some f → MulDivSummary f

/-- **The trusted base, precisely**, as `Assumptions` for `spec_of_verdict`: item 2 is
`AssumesHold` at every assume site, `MeetsContract` of every trusted internal body, `TrustedHold`
of the trusted external functions and `InterfaceEnsures`; item 3 `NoForeignWrites` of every call;
item 4 `KeccakSeparated` of the call's preimages; item 5 `AsmFree`; item 6 `MulDivSummary`; item 7
`ViewDeterministic` of every call. -/
def toAssumptions (scope : Call → Prop) (b : Bundle) (ctxOf : Call → Ctx) (step : GhostStep) :
    Assumptions where
  assumptionsHold call :=
    (∀ x ∈ H.assumeSites call, Core.AssumesHold x.1 x.2) ∧
    (∀ t ∈ H.trustedBodies, Core.MeetsContract t.1 t.2.1 t.2.2) ∧
    TrustedHold S p scope b ctxOf step H.trustedNames ∧
    InterfaceEnsures H.ifaceEns (H.transcript call)
  noDelegatecall := ∀ call, NoForeignWrites S p H.self (H.transcript call)
  keccakSeparated call := KeccakSeparated (H.keccakInputs call)
  asmSlotsDisjoint _ := AsmFree H.source
  asmMemorySafe _ := AsmFree H.source
  mulDiv := H.MulDivOk
  viewCalls := ∀ call, ViewDeterministic H.self (H.transcript call)

/-- The calls from a storage the contract's own functions reach from deployment: item 3 across
transactions. -/
def reachable (call : Call) : Prop := Reach S p H.deployed (slotValue call.storage)

/-- The plain instance: nothing hashed, every external call answered by default, no assumes, no
trusted functions, an assembly-free source `u`, no `Math.mulDiv`. -/
def plain (S : Sem) (p : S.Prog) (u : Solidity.SourceUnit) (deployed : Nat → Nat)
    (transcript : Call → Interaction.Transcript) : Hyps S p :=
  { keccakInputs := fun _ _ => False, transcript, self := default, deployed,
    ifaceEns := fun _ _ => False, assumeSites := fun _ => [], trustedBodies := [],
    trustedNames := [], source := u, mulDiv := none }

/-- **Discharged for a contract with no hashing, no external call that returns, no assume, no
trusted function, no assembly and no `Math.mulDiv`**: every hypothesis holds on every call. The
interface ensures are `False` here, so this holds only because no call returns. -/
theorem plain_on {S : Sem} {p : S.Prog} {u : Solidity.SourceUnit} {deployed : Nat → Nat}
    {transcript : Call → Interaction.Transcript} (hu : AsmFree u)
    (ht : ∀ call, DefaultCalls (transcript call)) (scope : Call → Prop) (b : Bundle)
    (ctxOf : Call → Ctx) (step : GhostStep) (call : Call) :
    ((plain S p u deployed transcript).toAssumptions scope b ctxOf step).On call := by
  refine ⟨⟨fun _ h => by simp [plain] at h, fun _ h => by simp [plain] at h, trustedHold_nil,
    interfaceEnsures_of_default (ht call)⟩, fun c => noForeignWrites_of_default (ht c),
    keccakSeparated_empty, hu, hu, fun _ h => by simp [plain] at h,
    fun c => viewDeterministic_of_default (ht c)⟩

/-- The empty transcript, of a call that makes no query. -/
theorem defaultCalls_nil : DefaultCalls [] := fun _ h => by simp [callsOf] at h

/-- **The whole structure is satisfiable**: on every call, in every semantics. -/
theorem satisfiable (S : Sem) (p : S.Prog) (scope : Call → Prop) (b : Bundle)
    (ctxOf : Call → Ctx) (step : GhostStep) :
    ∃ H : Hyps S p, ∀ call, (H.toAssumptions scope b ctxOf step).On call :=
  ⟨plain S p {} (fun _ => 0) (fun _ => []),
    plain_on (by decide) (fun _ => defaultCalls_nil) scope b ctxOf step⟩

end Hyps

/-- **The spec of the bytecode from solar-verify's verdict, under the precise trusted base**: as
`spec_of_verdict`, on the calls of the scope where every hypothesis of `H` holds. -/
theorem spec_of_verdict_hyps {S T : Sem} {p : S.Prog} {q : T.Prog} {scope : Call → Prop}
    {b : Bundle} {ctxOf : Call → Ctx} {step : GhostStep} (H : Hyps S p)
    (hwf : b.WF = true) (hopaque : OpaqueInRange b)
    (verdict : Verdict S p scope b ctxOf step (H.toAssumptions scope b ctxOf step))
    (stage : Stage S T p q scope) :
    Holds T q (fun call => scope call ∧ (H.toAssumptions scope b ctxOf step).On call) b ctxOf
      step :=
  spec_of_verdict hwf hopaque verdict stage

end SolidCore.Spec.TrustedBase
