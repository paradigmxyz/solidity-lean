import SolidCore.Refinement.ComposeSeq
import SolidCore.Refinement.Abi
import Verify.Basic
import EthLib.Cryptography.Hash.Sha256

/-!
# The final statement: a verified specification holds of deployed bytecode

This module states, once and for every contract, what the end-to-end certificate of a
compilation says, and proves how the stages of the pipeline compose into it.

## What is certified

A contract is runtime bytecode `code`, bound by a `Manifest` to the source's SHA-256, the
compiler's commit, its options and the bytecode's own SHA-256 (`Bound`, checked by the kernel
for the bytecode: its hex and its SHA-256 by EthLib's FIPS 180-4 implementation). Its
specification (`ContractSpec`) is solar-verify's, read over an abstract state `St` that the
storage layout gives from the slot function of a storage (`abs`): the contract invariants
(`@custom:invariant`) and, for each public or external function of the specification, its
selector, its ABI parameters, its precondition (`@custom:requires`) and its postcondition
(`@custom:ensures`, which may read `old` state, the new state and the return data).

`Certificate` holds two theorems about `code`:

* (a) **refinement** (`Agree`): on every call of a specified function, on any clean argument
  words, with any call value and from any storage, SolidCore's run of the checked contract and
  EthLib's run of `code` both finish and show the same observable: success, return or revert
  data, logs and the final storage. SolidCore and EthLib are deterministic, so this is both
  directions at once: every bytecode result is a source result (`Agree.backward`), reverts
  and exceptional halts included, and every source result is the bytecode's.
* (b) **the specification holds of the bytecode** (`Holds ethLib code spec`), in
  solar-verify's semantics: from a storage whose abstract state meets the invariants and the
  function's precondition, a call that returns meets the postcondition and the invariants, and
  a non-payable function returns only without value (so no balance moves); a call that fails,
  for any reason, leaves the storage as it was and logs nothing.

## Composition

`Stage A B p q scope` (SolarTV's, which every stage of the pipeline proves) only preserves the
results of runs of `p` that finish: when `p` finishes no call of the scope, every `q` is a
stage of it (`stage_of_never`). A stage chain therefore gives agreement only with the source's
termination (`agree_of_stage`), and a specification holds of the target only through
agreement (`Holds.of_agree`): partial correctness of a source that never finishes says nothing.
`certificate_of_stages` composes the source stage (SolidCore to lowered MIR: solidity-lean's
Generic stage), the backend (solar-tv: lowered MIR through scheduling and the EVM IR passes) and
the assembly stage (EVM IR to bytecode on EthLib) with the source's specification and
termination into (a) and (b).

## Out of gas

`Target.run` carries `gasLimit` gas. `Target.runWith gas` is the same run with any gas, and
`ethLibWith gas` its semantics. In solar-verify's semantics a failed call owes nothing but
rolling back, which `runWith` gives for every failure (`runWith_failure`), out of gas included.
So the specification holds at every gas (`Holds.allGas`) once every success at any gas is the
success at `gasLimit` (`GasStable`), and then every bytecode result at any gas is the source's
result or a failure that changes nothing (`RefinesAtAnyGas`, `refinesAtAnyGas`). `GasStable` is
a separate obligation; the stages prove the run at `gasLimit`.

## Transactions, external calls and reentrancy

`Holds.trace` lifts the invariants across transactions: on every sequence of calls of the
specification from a storage that meets the invariants, each call starting from the storage the
one before left (`Carries`), the invariants hold at the start of every call and each call whose
precondition holds there meets its specification. This is the whole story for code that runs in
one frame: `FrameLocal code` (decided by the kernel on the linear decoding of the bytecode, which
is every offset execution can reach) says the code has no instruction that runs other code or
reads state outside the frame (`CALL`, `CALLCODE`, `DELEGATECALL`, `STATICCALL`, `CREATE`,
`CREATE2`, `SELFDESTRUCT`, balances, other accounts' code, the block and transaction
environment, the caller and origin, `GAS`, transient storage). Then no other contract runs while
it does, so it cannot be reentered, and the fixed caller, callee and environment of `Target.run`
are not read. A contract that calls out or reads its environment fails the check, so no
certificate exists for it: the README's assumptions for external calls (the invariants hold
before each call, the storage is havocked across it) need a semantics with other frames, which
this one is not.

## Not covered

Deployment: `Target.run` starts from the runtime bytecode and the call's storage, so the
constructor's `@custom:ensures` and the invariants after deployment are the source's claims
about the first storage, not theorems about initcode. Calls outside the specified functions'
clean ABI encodings are outside the scope of (a) and (b) unless a contract's certificate widens
it.
-/

namespace SolidCore.Refinement.Final

open SolidCore.Refinement

/-! ## Agreement: refinement in both directions -/

/-- `q` agrees with `p` on `scope`: on every call of the scope both finish with the same
observable. -/
def Agree (A B : Sem) (p : A.Prog) (q : B.Prog) (scope : Call → Prop) : Prop :=
  ∀ call, scope call → ∃ obs, A.run p call = some obs ∧ B.run q call = some obs

/-- A stage whose source finishes every call of the scope is agreement. -/
theorem agree_of_stage {A B : Sem} {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    (stage : Stage A B p q scope) (fin : ∀ call, scope call → (A.run p call).isSome) :
    Agree A B p q scope := by
  intro call hc
  obtain ⟨obs, h⟩ := Option.isSome_iff_exists.mp (fin call hc)
  exact ⟨obs, h, stage call hc obs h⟩

/-- Agreement is a stage. -/
theorem Agree.stage {A B : Sem} {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    (h : Agree A B p q scope) : Stage A B p q scope := by
  intro call hc obs hobs
  obtain ⟨o, h1, h2⟩ := h call hc
  rw [Option.some.inj (hobs.symm.trans h1)]
  exact h2

/-- **Every result of the target is a result of the source.** -/
theorem Agree.backward {A B : Sem} {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    (h : Agree A B p q scope) {call : Call} (hc : scope call) {obs : Observable}
    (hq : B.run q call = some obs) : A.run p call = some obs := by
  obtain ⟨o, h1, h2⟩ := h call hc
  rw [Option.some.inj (hq.symm.trans h2)]
  exact h1

/-- The target finishes every call of the scope. -/
theorem Agree.finishes {A B : Sem} {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    (h : Agree A B p q scope) {call : Call} (hc : scope call) : (B.run q call).isSome := by
  obtain ⟨o, -, h2⟩ := h call hc
  simp [h2]

theorem Agree.trans {A B C : Sem} {p : A.Prog} {q : B.Prog} {r : C.Prog} {scope : Call → Prop}
    (first : Agree A B p q scope) (second : Agree B C q r scope) : Agree A C p r scope := by
  intro call hc
  obtain ⟨o, h1, h2⟩ := first call hc
  exact ⟨o, h1, second.stage call hc o h2⟩

theorem Agree.mono {A B : Sem} {p : A.Prog} {q : B.Prog} {scope narrower : Call → Prop}
    (h : Agree A B p q scope) (within : ∀ call, narrower call → scope call) :
    Agree A B p q narrower :=
  fun call hc => h call (within call hc)

/-- **What a stage alone does not say.** A source that finishes no call of the scope has a stage
to every target program, whatever it does. -/
theorem stage_of_never {A B : Sem} {p : A.Prog} (q : B.Prog) {scope : Call → Prop}
    (never : ∀ call, scope call → A.run p call = none) : Stage A B p q scope := by
  intro call hc obs h
  rw [never call hc] at h
  cases h

/-- Agreement rules that out on every call of its scope. -/
theorem Agree.not_never {A B : Sem} {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    (h : Agree A B p q scope) {call : Call} (hc : scope call) : A.run p call ≠ none := by
  obtain ⟨o, h1, -⟩ := h call hc
  simp [h1]

/-- `Refines` is agreement between SolidCore and EthLib. -/
theorem agree_iff_refines {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {code : ByteArray} {scope : Call → Prop} :
    Agree (solidCore fuel) ethLib c code scope ↔ Refines fuel c code scope := Iff.rfl

/-! ## Specifications -/

/-- A public or external function and its specification in solar-verify's terms, over the
abstract state `St`. -/
structure FnSpec (St : Type) where
  /-- The function's name, for reading only. -/
  name : String
  /-- Its selector. -/
  sel : Nat
  /-- Its ABI parameters. -/
  params : List Abi.Param
  /-- `@custom:requires`: of the argument words and the state before the call. -/
  requires : List Nat → St → Prop
  /-- `@custom:ensures`: of the argument words, the state before the call (`old`), the state
  after it and the return data. -/
  ensures : List Nat → St → St → List Nat → Prop
  /-- Whether the function is `payable`. -/
  payable : Bool

/-- A contract's specification: its storage layout, as the abstract state of a storage read
slot by slot, its invariants and its functions' specifications. -/
structure ContractSpec (St : Type) where
  abs : (Nat → Nat) → St
  invariant : St → Prop
  fns : List (FnSpec St)

namespace FnSpec

variable {St : Type}

/-- The argument words are a clean ABI encoding of the parameters. -/
def Typed (f : FnSpec St) (args : List Nat) : Prop :=
  List.Forall₂ (fun (p : Abi.Param) (a : Nat) => p.clean a = true) f.params args

/-- The call of `f` on `args` with `value` wei from the storage `storage`. -/
def call (f : FnSpec St) (args : List Nat) (value : Nat) (storage : List (Nat × Nat)) : Call :=
  { calldata := Abi.calldata f.sel args, callvalue := value, storage }

end FnSpec

namespace ContractSpec

variable {St : Type}

/-- The abstract state of the storage a call starts from. -/
def pre (spec : ContractSpec St) (call : Call) : St := spec.abs (slotValue call.storage)

/-- The calls of the specification: a specified function, on clean argument words, with any
value below `2 ^ 256`, from any storage. -/
def Calls (spec : ContractSpec St) (call : Call) : Prop :=
  ∃ f ∈ spec.fns, ∃ args, f.Typed args ∧ ∃ v, v < 2 ^ 256 ∧ ∃ σ, call = f.call args v σ

/-- What solar-verify promises of a call of `f` on `args` that shows `obs`: a return meets the
postcondition and the invariants, and is without value unless `f` is payable; a failure, for any
reason, leaves the storage and logs nothing. -/
def Outcome (spec : ContractSpec St) (f : FnSpec St) (args : List Nat) (call : Call)
    (obs : Observable) : Prop :=
  (obs.success = true →
    f.ensures args (spec.pre call) (spec.abs obs.storage) obs.output ∧
      spec.invariant (spec.abs obs.storage) ∧ (f.payable = false → call.callvalue = 0)) ∧
  (obs.success = false → obs.storage = slotValue call.storage ∧ obs.logs = [])

end ContractSpec

open ContractSpec

/-- **The specification holds of `p`**, in solar-verify's semantics (partial correctness): every
result `p` shows for a call of a specified function from a storage that meets the invariants
and the precondition meets `Outcome`. -/
def Holds {St : Type} (S : Sem) (p : S.Prog) (spec : ContractSpec St) : Prop :=
  ∀ f ∈ spec.fns, ∀ args, f.Typed args → ∀ v, v < 2 ^ 256 → ∀ σ,
    spec.invariant (spec.abs (slotValue σ)) → f.requires args (spec.abs (slotValue σ)) →
    ∀ obs, S.run p (f.call args v σ) = some obs → spec.Outcome f args (f.call args v σ) obs

/-- A specification holds of every program that agrees with one it holds of. -/
theorem Holds.of_agree {St : Type} {A B : Sem} {p : A.Prog} {q : B.Prog} {spec : ContractSpec St}
    (h : Holds A p spec) (agree : Agree A B p q spec.Calls) : Holds B q spec := by
  intro f hf args ht v hv σ hinv hreq obs hrun
  exact h f hf args ht v hv σ hinv hreq obs
    (agree.backward ⟨f, hf, args, ht, v, hv, σ, rfl⟩ hrun)

/-! ## Composition -/

/-- **The composition.** A specification SolidCore's contract meets and finishes, and the stages
from SolidCore to lowered MIR, through the backend to EVM IR and from EVM IR to the bytecode on
EthLib, on the specification's calls, give (a) agreement of the bytecode with the source and (b)
the specification on the bytecode. -/
theorem certificate_of_stages {St : Type} {fuel : Nat} {mirSem evmirSem : Sem}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} {mir : mirSem.Prog} {evmir : evmirSem.Prog}
    {code : ByteArray} {spec : ContractSpec St}
    (source : Holds (solidCore fuel) c spec)
    (fin : ∀ call, spec.Calls call → (Source.run fuel c call).isSome)
    (lowering : Stage (solidCore fuel) mirSem c mir spec.Calls)
    (backend : Stage mirSem evmirSem mir evmir spec.Calls)
    (assembly : Stage evmirSem ethLib evmir code spec.Calls) :
    Agree (solidCore fuel) ethLib c code spec.Calls ∧ Holds ethLib code spec := by
  have agree := agree_of_stage ((lowering.trans backend).trans assembly) fin
  exact ⟨agree, source.of_agree agree⟩

/-! ## What each half alone does not say -/

/-- **Partial correctness alone is weak.** Code that fails every call, rolling back, meets every
specification in solar-verify's semantics: this is why a certificate carries agreement too. -/
theorem Holds.of_fails {St : Type} {S : Sem} {p : S.Prog} (spec : ContractSpec St)
    (fails : ∀ call obs, S.run p call = some obs →
      obs.success = false ∧ obs.storage = slotValue call.storage ∧ obs.logs = []) :
    Holds S p spec := by
  intro f _ args _ v _ σ _ _ obs hrun
  obtain ⟨hs, hst, hl⟩ := fails _ obs hrun
  exact ⟨fun h => absurd (hs.symm.trans h) (by decide), fun _ => ⟨hst, hl⟩⟩

/-! ## Any source semantics -/

/-- The composition for any source semantics \`S\`, such as SolidCore with as much fuel as a call
needs (\`solidCoreAny\`). -/
theorem compose {St : Type} {S mirSem evmirSem : Sem} {p : S.Prog} {mir : mirSem.Prog}
    {evmir : evmirSem.Prog} {code : ByteArray} {spec : ContractSpec St}
    (source : Holds S p spec) (fin : ∀ call, spec.Calls call → (S.run p call).isSome)
    (lowering : Stage S mirSem p mir spec.Calls) (backend : Stage mirSem evmirSem mir evmir spec.Calls)
    (assembly : Stage evmirSem ethLib evmir code spec.Calls) :
    Agree S ethLib p code spec.Calls ∧ Holds ethLib code spec := by
  have agree := agree_of_stage ((lowering.trans backend).trans assembly) fin
  exact ⟨agree, source.of_agree agree⟩

open Classical in
/-- SolidCore with as much fuel as the call needs: the run at the least fuel that finishes it.
A contract whose loops run as many times as an argument says finishes no such call at any fixed
fuel for every argument, while it finishes each call at some fuel. -/
noncomputable def solidCoreAny : Sem where
  Prog := SolidCore.Solidity.TypeCheck.CheckedContract
  run c call := if h : ∃ n, (Source.run n c call).isSome then Source.run (Nat.find h) c call else none

/-- More fuel does not change a finished run of SolidCore: the statement at \`Source.run\` of the
source interpreter's fuel monotonicity (\`SolidCore.Solidity.FuelMonotonicity\` proves it for the
interpreter's trees). -/
def FuelStable (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Prop :=
  ∀ n m call obs, n ≤ m → Source.run n c call = some obs → Source.run m c call = some obs

/-- A run of SolidCore at a fixed fuel is the run with as much fuel as it needs. -/
theorem solidCoreAny_run {c : SolidCore.Solidity.TypeCheck.CheckedContract} (stable : FuelStable c)
    {fuel : Nat} {call : Call} {obs : Observable} (h : Source.run fuel c call = some obs) :
    solidCoreAny.run c call = some obs := by
  classical
  have hex : ∃ n, (Source.run n c call).isSome := ⟨fuel, by simp [h]⟩
  show (if h : ∃ n, (Source.run n c call).isSome then Source.run (Nat.find h) c call else none) = _
  rw [dif_pos hex]
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hex)
  have hle : Nat.find hex ≤ fuel := Nat.find_min' hex (by simp [h])
  rw [ho]
  have := stable _ _ _ _ hle ho
  rw [h] at this
  exact this.symm

/-- The stage from SolidCore at a fixed fuel to SolidCore with as much fuel as a call needs. -/
theorem stage_solidCoreAny {c : SolidCore.Solidity.TypeCheck.CheckedContract} (stable : FuelStable c)
    (fuel : Nat) (scope : Call → Prop) : Stage (solidCore fuel) solidCoreAny c c scope :=
  fun _ _ _ h => solidCoreAny_run stable h

/-! ## Loom: the source obligation from a triple -/

/-- **The source obligation from Loom.** A triple `{pre} c {post}` against SolidCore on the
specification's calls (`SolidCore.Verify.Triple`, which `triple_of_wp` gives from Loom's weakest
precondition of a model), whose precondition every specified call from a storage meeting the
invariants and the function's precondition meets, and whose postcondition gives `Outcome` there,
gives the specification on SolidCore. -/
theorem Holds.of_triple {St : Type} {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {spec : ContractSpec St} {pre : Call → Prop} {post : Call → Observable → Prop}
    (h : SolidCore.Verify.Triple fuel c spec.Calls pre post)
    (hpre : ∀ f ∈ spec.fns, ∀ args, f.Typed args → ∀ v, v < 2 ^ 256 → ∀ σ,
      spec.invariant (spec.abs (slotValue σ)) → f.requires args (spec.abs (slotValue σ)) →
        pre (f.call args v σ))
    (hpost : ∀ f ∈ spec.fns, ∀ args, f.Typed args → ∀ v, v < 2 ^ 256 → ∀ σ,
      spec.invariant (spec.abs (slotValue σ)) → f.requires args (spec.abs (slotValue σ)) →
        ∀ obs, post (f.call args v σ) obs → spec.Outcome f args (f.call args v σ) obs) :
    Holds (solidCore fuel) c spec := by
  intro f hf args ht v hv σ hinv hreq obs hrun
  have hc : spec.Calls (f.call args v σ) := ⟨f, hf, args, ht, v, hv, σ, rfl⟩
  exact hpost f hf args ht v hv σ hinv hreq obs
    ((h _ hc (hpre f hf args ht v hv σ hinv hreq)).2 obs hrun)

/-- A triple whose precondition holds on every call of the specification gives the source's
termination there, which agreement needs (`agree_of_stage`). -/
theorem finishes_of_triple {St : Type} {fuel : Nat}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} {spec : ContractSpec St}
    {post : Call → Observable → Prop}
    (h : SolidCore.Verify.Triple fuel c spec.Calls (fun _ => True) post) :
    ∀ call, spec.Calls call → (Source.run fuel c call).isSome :=
  fun call hc => (h call hc trivial).1

/-! ## Transactions -/

/-- One call of a sequence: the function, its argument words and the call value. -/
structure Step (St : Type) where
  f : FnSpec St
  args : List Nat
  value : Nat

/-- A sequence of calls run with `run` from `σ`, each from the storage `carry` gives after the one
before: the invariants hold at the start of every call reached, and every call whose precondition
holds there meets its specification on whatever it shows. -/
def Trace {St : Type} (spec : ContractSpec St) (run : Call → Option Observable) (carry : Carry) :
    List (Nat × Nat) → List (Step St) → Prop
  | _, [] => True
  | σ, s :: rest => spec.invariant (spec.abs (slotValue σ)) ∧
      (s.f.requires s.args (spec.abs (slotValue σ)) →
        ∀ obs, run (s.f.call s.args s.value σ) = some obs →
          spec.Outcome s.f s.args (s.f.call s.args s.value σ) obs ∧
            Trace spec run carry (carry (s.f.call s.args s.value σ) obs) rest)

/-- **The invariants across transactions.** When the specification holds of `p` and the storage
carried to each call is exactly the storage the call before left, every sequence of specified
calls from a storage that meets the invariants is a `Trace`. -/
theorem Holds.trace {St : Type} {S : Sem} {p : S.Prog} {spec : ContractSpec St} {carry : Carry}
    (h : Holds S p spec) (exact : ∀ call obs, S.run p call = some obs → Carries carry call obs) :
    ∀ σ (steps : List (Step St)), spec.invariant (spec.abs (slotValue σ)) →
      (∀ s ∈ steps, s.f ∈ spec.fns ∧ s.f.Typed s.args ∧ s.value < 2 ^ 256) →
      Trace spec (S.run p) carry σ steps := by
  intro σ steps
  induction steps generalizing σ with
  | nil => intro _ _; trivial
  | cons s rest ih =>
    intro hinv hsteps
    obtain ⟨hf, ht, hv⟩ := hsteps s List.mem_cons_self
    refine ⟨hinv, fun hreq obs hrun => ?_⟩
    have hout := h s.f hf s.args ht s.value hv σ hinv hreq obs hrun
    refine ⟨hout, ih _ ?_ fun s' hs' => hsteps s' (List.mem_cons_of_mem _ hs')⟩
    rw [exact _ _ hrun]
    cases hs : obs.success
    · rw [(hout.2 hs).1]
      exact hinv
    · exact (hout.1 hs).2.1

/-! ## Gas -/

namespace Target

open EthLib.Base EthLib.Execution EthLib.Execution.Evm

/-- The message of `Target.message` with `gas` gas. -/
def messageWith (gas : Nat) (code : ByteArray) (call : Call) : Message .fusaka :=
  { Refinement.Target.message code call with gas }

/-- `Target.run` with the message `msg`. -/
def runMsg (msg : Message .fusaka) (code : ByteArray) (call : Call) : Option Observable :=
  match processMessage (Meter := Nat) .fusaka msg (Refinement.Target.preState code call)
      Substate.empty with
  | .error _ => none
  | .ok ⟨evm, _⟩ =>
    let success := evm.error.isNone
    some
      { success
        output := evm.output.toList.map (·.toNat)
        logs :=
          if success then
            evm.substate.logs.toList.map fun log =>
              (log.topics.map fun topic => bytesToNat topic.toList,
                log.data.toList.map (·.toNat))
          else []
        storage := fun slot =>
          if success then
            (evm.state.getStorage (Refinement.Target.address selfAddress)
              (Refinement.Target.storageKey slot)).toNat
          else slotValue call.storage slot }

/-- `Target.run` with `gas` gas. -/
def runWith (gas : Nat) (code : ByteArray) (call : Call) : Option Observable :=
  runMsg (messageWith gas code call) code call

theorem messageWith_gasLimit (code : ByteArray) (call : Call) :
    messageWith gasLimit code call = Refinement.Target.message code call := rfl

theorem runMsg_message (code : ByteArray) (call : Call) :
    runMsg (Refinement.Target.message code call) code call = Refinement.Target.run code call := by
  unfold runMsg Refinement.Target.run
  split <;> rename_i h <;> rw [h]

theorem runWith_gasLimit (code : ByteArray) (call : Call) :
    runWith gasLimit code call = Refinement.Target.run code call := by
  unfold runWith
  rw [messageWith_gasLimit]
  exact runMsg_message code call

/-- A failed run, at any gas and for any reason, out of gas included, leaves the storage as it
was and logs nothing. -/
theorem runWith_failure {gas : Nat} {code : ByteArray} {call : Call} {obs : Observable}
    (h : runWith gas code call = some obs) (hf : obs.success = false) :
    obs.storage = slotValue call.storage ∧ obs.logs = [] := by
  unfold runWith runMsg at h
  split at h
  · cases h
  · cases h
    simp only at hf
    simp [hf]

end Target

/-- EthLib on runtime bytecode with `gas` gas. -/
def ethLibWith (gas : Nat) : Sem := { Prog := ByteArray, run := Target.runWith gas }

/-- Every success at any gas, on a call of the scope, is the success at `gasLimit`. -/
def GasStable (code : ByteArray) (scope : Call → Prop) : Prop :=
  ∀ gas call obs, scope call → Target.runWith gas code call = some obs → obs.success = true →
    Refinement.Target.run code call = some obs

/-- **The specification at every gas.** -/
theorem Holds.allGas {St : Type} {code : ByteArray} {spec : ContractSpec St}
    (h : Holds ethLib code spec) (stable : GasStable code spec.Calls) (gas : Nat) :
    Holds (ethLibWith gas) code spec := by
  intro f hf args ht v hv σ hinv hreq obs hrun
  change Target.runWith gas code _ = some obs at hrun
  cases hs : obs.success
  · exact ⟨fun h' => absurd (hs.symm.trans h') (by decide),
      fun _ => Target.runWith_failure hrun hs⟩
  · exact h f hf args ht v hv σ hinv hreq obs
      (stable gas _ obs ⟨f, hf, args, ht, v, hv, σ, rfl⟩ hrun hs)

/-- Every result of the bytecode, at any gas, on a call of the scope, is the source's result or a
failure that leaves the storage and logs nothing. -/
def RefinesAtAnyGas (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract)
    (code : ByteArray) (scope : Call → Prop) : Prop :=
  ∀ gas call obs, scope call → Target.runWith gas code call = some obs →
    Source.run fuel c call = some obs ∨
      (obs.success = false ∧ obs.storage = slotValue call.storage ∧ obs.logs = [])

theorem refinesAtAnyGas {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {code : ByteArray} {scope : Call → Prop} (agree : Agree (solidCore fuel) ethLib c code scope)
    (stable : GasStable code scope) : RefinesAtAnyGas fuel c code scope := by
  intro gas call obs hc hrun
  cases hs : obs.success
  · exact Or.inr ⟨rfl, Target.runWith_failure hrun hs⟩
  · exact Or.inl (agree.backward hc (stable gas call obs hc hrun hs))

/-! ## The code runs in one frame -/

/-- The bytes of the immediate of an opcode: `PUSH1` to `PUSH32` take 1 to 32. -/
def immediate (op : Nat) : Nat := if 0x60 ≤ op ∧ op ≤ 0x7f then op - 0x5f else 0

/-- The opcodes of the linear decoding of `bytes`, skipping push immediates: every offset
execution can reach, as a jump into an immediate is not a valid jump destination. -/
def opsFrom : Nat → List Nat → List Nat
  | 0, _ => []
  | _, [] => []
  | n + 1, op :: rest => op :: opsFrom n (rest.drop (immediate op))

/-- The opcodes of `code`. -/
def opcodes (code : ByteArray) : List Nat := opsFrom code.size (code.data.toList.map (·.toNat))

/-- Opcodes that run other code or read state outside the frame: `ADDRESS`, `BALANCE`,
`ORIGIN`, `CALLER`, `GASPRICE`, `EXTCODESIZE`, `EXTCODECOPY`, `EXTCODEHASH`, the block's
`BLOCKHASH` to `BLOBBASEFEE` (`SELFBALANCE` among them), `GAS`, `TLOAD`, `TSTORE`, `CREATE`,
`CALL`, `CALLCODE`, `DELEGATECALL`, `CREATE2`, `STATICCALL` and `SELFDESTRUCT`. -/
def outsideFrame : List Nat :=
  [0x30, 0x31, 0x32, 0x33, 0x3a, 0x3b, 0x3c, 0x3f, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46,
    0x47, 0x48, 0x49, 0x4a, 0x5a, 0x5c, 0x5d, 0xf0, 0xf1, 0xf2, 0xf4, 0xf5, 0xfa, 0xff]

/-- `code` runs in one frame and reads nothing of its environment but its call. -/
def FrameLocal (code : ByteArray) : Bool := (opcodes code).all fun op => !outsideFrame.contains op

/-! ## Binding -/

/-- What a certificate is bound to. -/
structure Manifest where
  contract : String
  sourceSha256 : String
  compilerCommit : String
  options : List String
  runtimeHex : String
  runtimeSha256 : String

/-- The lowercase hex of bytes. -/
def hexOf (bytes : List Nat) : String :=
  String.join (bytes.map fun b =>
    let d := fun n : Nat => if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
    String.ofList [d (b / 16 % 16), d (b % 16)])

/-- The bytes of a hex string, two digits a byte. -/
def bytesOfHex (s : String) : ByteArray :=
  let digit (c : Char) : Nat :=
    if '0' ≤ c ∧ c ≤ '9' then c.toNat - 48 else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87 else 0
  let rec go : List Char → List UInt8
    | a :: b :: rest => (digit a * 16 + digit b).toUInt8 :: go rest
    | _ => []
  ⟨(go s.toList).toArray⟩

/-- The bytecode is the manifest's: its hex and its SHA-256. -/
def Bound (m : Manifest) (code : ByteArray) : Prop :=
  hexOf (code.data.toList.map (·.toNat)) = m.runtimeHex ∧
    hexOf ((EthLib.Cryptography.Hash.Sha256.hash code).data.toList.map (·.toNat)) = m.runtimeSha256

/-- **The certificate of a compilation**: the bytecode bound to its manifest, running in one
frame, (a) agreeing with SolidCore's checked contract on every call of the specification, and
(b) meeting the specification, which SolidCore's contract meets too. -/
structure Certificate {St : Type} (spec : ContractSpec St) (m : Manifest) where
  code : ByteArray
  fuel : Nat
  source : SolidCore.Solidity.TypeCheck.CheckedContract
  bound : Bound m code
  frameLocal : FrameLocal code = true
  sourceHolds : Holds (solidCore fuel) source spec
  refines : Agree (solidCore fuel) ethLib source code spec.Calls
  holds : Holds ethLib code spec

/-! ## Refinement with out of gas -/

/-- **Every result of `q` on the scope is a result of `p`, or a failure that leaves the storage
and logs nothing**: the direction of refinement that admits running out of gas, or any other
exceptional halt, where the source does not. -/
def Within (A B : Sem) (p : A.Prog) (q : B.Prog) (scope : Call → Prop) : Prop :=
  ∀ call, scope call → ∀ obs, B.run q call = some obs →
    A.run p call = some obs ∨ (obs.success = false ∧ obs.storage = slotValue call.storage ∧ obs.logs = [])

theorem Agree.within {A B : Sem} {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    (h : Agree A B p q scope) : Within A B p q scope :=
  fun _ hc _ hq => Or.inl (h.backward hc hq)

/-- Agreement, then refinement with failures. -/
theorem Agree.trans_within {A B C : Sem} {p : A.Prog} {q : B.Prog} {r : C.Prog}
    {scope : Call → Prop} (first : Agree A B p q scope) (second : Within B C q r scope) :
    Within A C p r scope := by
  intro call hc obs hr
  rcases second call hc obs hr with h | h
  · exact Or.inl (first.backward hc h)
  · exact Or.inr h

/-- A specification holds of every program within one it holds of. -/
theorem Holds.of_within {St : Type} {A B : Sem} {p : A.Prog} {q : B.Prog} {spec : ContractSpec St}
    (h : Holds A p spec) (within : Within A B p q spec.Calls) : Holds B q spec := by
  intro f hf args ht v hv σ hinv hreq obs hrun
  rcases within _ ⟨f, hf, args, ht, v, hv, σ, rfl⟩ obs hrun with h' | ⟨hs, hst, hl⟩
  · exact h f hf args ht v hv σ hinv hreq obs h'
  · exact ⟨fun h'' => absurd (hs.symm.trans h'') (by decide), fun _ => ⟨hst, hl⟩⟩

/-- With enough gas, the bytecode shows exactly what the source does: every call of the scope has
a gas from which on `runWith` gives the source's result. -/
def EventuallyAgree (S : Sem) (p : S.Prog) (code : ByteArray) (scope : Call → Prop) : Prop :=
  ∀ call, scope call → ∃ obs G, S.run p call = some obs ∧ ∀ gas, G ≤ gas →
    Target.runWith gas code call = some obs

/-- **The composition at every gas.** A specification the source meets and finishes, the stages
from the source to lowered MIR and through the backend to EVM IR, and an assembly stage that at
every gas gives the EVM IR's result or a failure, give at every gas: every result of the bytecode
is the source's or a failure that changes nothing, and the specification holds of the bytecode. -/
theorem compose_anyGas {St : Type} {S mirSem evmirSem : Sem} {p : S.Prog} {mir : mirSem.Prog}
    {evmir : evmirSem.Prog} {code : ByteArray} {spec : ContractSpec St}
    (source : Holds S p spec) (fin : ∀ call, spec.Calls call → (S.run p call).isSome)
    (lowering : Stage S mirSem p mir spec.Calls) (backend : Stage mirSem evmirSem mir evmir spec.Calls)
    (assembly : ∀ gas, Within evmirSem (ethLibWith gas) evmir code spec.Calls) (gas : Nat) :
    Within S (ethLibWith gas) p code spec.Calls ∧ Holds (ethLibWith gas) code spec := by
  have agree := agree_of_stage (lowering.trans backend) fin
  have within := agree.trans_within (assembly gas)
  exact ⟨within, source.of_within within⟩

/-- At `gasLimit`, a stage into EthLib is a stage into `ethLibWith gasLimit`. -/
theorem stage_ethLibWith_gasLimit {A : Sem} {p : A.Prog} {code : ByteArray} {scope : Call → Prop}
    (h : Stage A ethLib p code scope) : Stage A (ethLibWith gasLimit) p code scope := by
  intro call hc obs hobs
  show Target.runWith gasLimit code call = some obs
  rw [Target.runWith_gasLimit]
  exact h call hc obs hobs

/-- **The certificate of a compilation at every gas**, for code whose gas use the call's arguments
bound, such as a loop over one: the bytecode bound to its manifest, running in one frame; at every
gas, every result is SolidCore's (with as much fuel as the call needs) or a failure that changes
nothing; with enough gas, it is SolidCore's; and the specification holds of SolidCore and of the
bytecode at every gas. -/
structure CertificateAnyGas {St : Type} (spec : ContractSpec St) (m : Manifest) where
  code : ByteArray
  source : SolidCore.Solidity.TypeCheck.CheckedContract
  bound : Bound m code
  frameLocal : FrameLocal code = true
  sourceHolds : Holds solidCoreAny source spec
  within : ∀ gas, Within solidCoreAny (ethLibWith gas) source code spec.Calls
  enough : EventuallyAgree solidCoreAny source code spec.Calls
  holds : ∀ gas, Holds (ethLibWith gas) code spec

end SolidCore.Refinement.Final
