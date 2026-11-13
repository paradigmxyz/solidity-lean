import SolidCore.Refinement.Solar.W4Lowering
import SolidCore.Verify.W4
import SolidCore.Refinement.Evm.WideStorage
import SolidCore.Refinement.Spec
import w4.Proofs
import w4.gen.Main.Manifest

/-!
# The w4 milestone: solar's bytecode meets w4's verified specification, every stage proved

The contract (scripts/refinement/corpus/w4.sol; solar-tv/milestone/w4/w4.sol in solar's tree,
the same contract),

    contract Main { uint256 x; function set(uint256 v) external { x = v; } }

compiled by solar (-Ogas --evm-version osaka) to the 36 bytes of runtime bytecode
Corpus.W4.code, which is the bytecode solar exported with its stages (bytes_exported) and the
corpus's own compilation of w4.sol at solar 9688f215 (Bytecode.W4). certified states, with no
hypothesis, that this bytecode meets w4's specification (Verify.W4: set(v) succeeds with no
output and no logs, and leaves v in slot 0 and 0 elsewhere) on EthLib, and certifiedAt the same
from any storage (Verify.W4.postAt: v in slot 0, every other slot kept). The specification is
proved of SolidCore's checked contract with the Loom VC generator (Verify.W4.satisfies,
satisfiesAt) and carried to the bytecode through solar's actual pipeline (bytecode_of_stages),
every stage a theorem:

* source: SolidCore to the first lowered MIR, lower-abi and lower-dispatch included
  (lowering, loweringAt, SolidCore/Refinement/Solar/W4Lowering.lean, from the generic source
  stage SolidCore.Refinement.Generic.stage);
* backend: the first lowered MIR through stack scheduling and the four EVM IR passes to the
  final EVM IR (SolarTV.Milestone.W4.w4_mir_to_evmir, solar-tv/milestone/w4/Proofs, on every
  call: any call data, call value and storage);
* assembly: the final EVM IR to the bytecode on EthLib (stage, stageAt, below).

The stages hold under every oracle of SolarTV's semantics; the composition uses oracle, the
environment of EthLib's call.

## The assembly stage

* evmir_run_at: SolarTV's EVM IR semantics runs evm4 on every call of set(v) from any storage
  σ to expectedAt σ v: SolidCore's run (source_run_at, from Verify.W4.run_set_at) carried
  through the source stage (mir_run_at) and the backend stages.
* target_run_at: EthLib runs the bytecode on the same call to expectedAt σ v: every opcode
  stepped by EthLib's program logic from pc 0 with 10M gas (wide_tgt_at: SSTORE's write and
  price included, STOP against the observable, the call's storage σ read through
  Target.preState), its branches decided from the call data.
* stageAt and stage: the stage on Verify.W4.scopeAt and Verify.W4.scope, under every oracle.

solar-tv's SolarTV.Milestone.W4.decodes separately checks the bytecode's linear decoding
against evm4's instructions, the walk of the assembly checker.

## Scope

* Syntax: this one contract. The certificate is translation validation of this compilation.
* Calls: one call of set (selector 0x60fe47b1) with well-formed call data, the selector and one
  word below 2^256 (36 bytes; Abi.fullScope). Malformed call data, other selectors and nonzero
  call value are outside the scope.
* Storage: the deployed (empty) storage for certified, any storage for certifiedAt. The write
  of slot 0 is proved on every slot of the final storage in SolidCore, the MIR and EVM IR
  semantics and EthLib.
* EVM: EthLib at Fusaka, one message frame from 0x2000 to 0x1000 with 10M gas, metered on every
  step.

## Unverified boundaries

As for w5 (SolidCore/Refinement/Solar/Milestone.lean): the front end that parses w4.sol into
SolidCore (Source.W4), the exporter's printing of solar's IR as Lean (solar-tv/milestone/w4/gen),
and the semantics themselves.

No sorry, native_decide or bv_decide: the theorems depend on propext, Quot.sound and
Classical.choice only (pinned below).
-/

namespace SolidCore.Refinement.Solar.W4

open EthLib.Base EthLib.Execution EthLib.Execution.Evm
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm
open SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Wide

/-- The selector of set(uint256). -/
abbrev setSelector : Nat := Bytecode.W4.Main.setSelector

/-! ## The calls of the scope and what they show -/

theorem scopeAt_callAt {call : Call} (h : Verify.W4.scopeAt call) :
    ∃ (v : U256) (σ : List (Nat × Nat)), call = callAt setSelector [v] σ := by
  obtain ⟨σ, fn, hfn, args, hlen, hlt, rfl⟩ := h
  simp only [Corpus.W4.fns, List.mem_singleton] at hfn
  subst hfn
  match args, hlen with
  | [a], _ =>
    refine ⟨BitVec.ofNat 256 a, σ, ?_⟩
    have ha : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (hlt a (by simp))
    simp only [callAt, List.map_cons, List.map_nil, BitVec.toNat_ofNat, ha]

/-- The deployed scope is the scope from any storage at the deployed storage, none. -/
theorem scopeAt_of_scope {call : Call} (h : Verify.W4.scope call) : Verify.W4.scopeAt call :=
  ⟨[], h⟩

/-- What set(v) from the storage σ shows: success with no output and no logs, v in slot 0 and
every other slot of σ kept. -/
def expectedAt (σ : List (Nat × Nat)) (v : U256) : Observable :=
  { success := true, output := [], logs := [],
    storage := fun slot => if slot % 2 ^ 256 = 0 then v.toNat else slotValue σ slot }

/-- The model SolidCore runs set as, from the storage σ, shows expectedAt σ v. -/
theorem observe_model_at (v : U256) (σ : List (Nat × Nat)) :
    Verify.observe (slotValue σ) (Verify.W4.model [v.toNat] (slotValue σ)) = expectedAt σ v := by
  simp only [Verify.W4.model, Verify.observe, Verify.sstore, bind, StateT.bind, pure, StateT.pure,
    Except.bind, Except.pure, expectedAt, List.getD_cons_zero, Nat.zero_mod,
    Nat.mod_eq_of_lt v.isLt]

/-- SolidCore runs w4's set on any argument word from any storage σ to expectedAt σ v
(Verify.W4.run_set_at). -/
theorem source_run_at {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Corpus.W4.contract? = .ok c) (v : U256) (σ : List (Nat × Nat)) :
    Source.run Corpus.W4.fuel c (callAt setSelector [v] σ) = some (expectedAt σ v) := by
  obtain ⟨hk, _, hemp⟩ := Corpus.W4.shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  have := Verify.W4.run_set_at hk (Verify.deployedAt_of_deployed hd) v σ
  rw [observe_model_at] at this
  exact this

/-- SolarTV's lowered MIR semantics runs w4's first lowered MIR module on every call of set(v)
from any storage σ, under every oracle, to expectedAt σ v: SolidCore's run carried by the
generic source stage (loweringAt, Solar/W4Lowering.lean). -/
theorem mir_run_at (o : SolarTV.Machine.Oracle) (v : U256) (σ : List (Nat × Nat)) :
    (SolarTV.MIR.Lowered.moduleSem o).run SolarTV.Export.Main.stage0 (callAt setSelector [v] σ) =
      some (expectedAt σ v) := by
  obtain ⟨c, hc, -⟩ := Verify.W4.satisfies
  exact loweringAt o hc _ ⟨σ, _, List.mem_singleton_self _, [v.toNat], rfl,
    by simpa using v.isLt, rfl⟩ _ (source_run_at hc v σ)

/-! ## The bytecode -/

/-- The runtime bytecode's bytes. -/
def bytes : List Nat := Corpus.W4.code.data.toList.map (·.toNat)

/-- The corpus's bytecode is the bytecode solar exported with w4's stages. -/
theorem bytes_exported : bytes = SolarTV.Export.Main.bytecode := by decide

/-- The runtime bytecode as hex, as the manifest records it. -/
def runtimeHex : String := "346020575f3560e01c806360fe47b103602057602436106020576004355f55005b5f5ffd"

/-- SolarTV's EVM IR semantics runs w4's final EVM IR on every call of set(v) from any storage
σ, under every oracle, to the observable expectedAt σ v. -/
theorem evmir_run_at (o : SolarTV.Machine.Oracle) (v : U256) (σ : List (Nat × Nat)) :
    (SolarTV.evmirSem o).run SolarTV.Export.Main.evm4 (callAt setSelector [v] σ) =
      some (expectedAt σ v) :=
  SolarTV.Milestone.W4.w4_mir_to_evmir o _ trivial _ (mir_run_at o v σ)

section Target

open EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Symex SolidCore.Refinement.Evm.Logic

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- EthLib runs solar's bytecode on every call of set(v) from any storage σ to the observable
expectedAt σ v. -/
theorem target_run_at (v : U256) (σ : List (Nat × Nat)) :
    Target.run Corpus.W4.code (callAt setSelector [v] σ) = some (expectedAt σ v) := by
  have he : expectedAt σ v = ⟨true, [], [],
      fun slot => if slot % 2 ^ 256 = 0 then v.toNat else slotValue σ slot⟩ := rfl
  rw [he]
  refine run_of_postS_at Corpus.W4.code setSelector [v] σ _ rfl (fun h => by cases h) ?_
  intro msg hv hd hstat htgt
  have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
  simp only [Bytecode.W4.Main.setSelector] at hd
  repeat wide_one_at [Corpus.W4.code, Bytecode.W4.Main.runtimeNat, Bytecode.W4.Main.runtimeSize,
    Bytecode.W4.Main.setSelector] [hd, hv] hfork hstat htgt
  refine stop_postS ?lt ?op ?succ ?out rfl ?store
  case lt => evm_code [Corpus.W4.code, Bytecode.W4.Main.runtimeNat, Bytecode.W4.Main.runtimeSize]
  case op => evm_code [Corpus.W4.code, Bytecode.W4.Main.runtimeNat, Bytecode.W4.Main.runtimeSize]
  case succ => rfl
  case out => rfl
  case store =>
    intro slot
    simp only [htgt, getStorage_writeOf_of, getStorage_recordStorageRead, getStorage_preState_ofNat,
      storage_callAt, true_and, storageKey_eq_toBeBytes, BitVec.toNat_ofNat]
    simp only [Nat.reducePow, Nat.zero_mod]
    by_cases h : slot %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (slotValue_lt σ slot)

end Target

/-! ## The assembly stage -/

/-- **The assembly stage of w4 from any storage**: EVM IR to bytecode on EthLib, on every call
of set with no value from any storage, under every oracle. -/
theorem stageAt (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Main.evm4 Corpus.W4.code
      Verify.W4.scopeAt := by
  intro call hc obs hrun
  obtain ⟨v, σ, rfl⟩ := scopeAt_callAt hc
  rw [evmir_run_at o v σ] at hrun
  cases hrun
  exact target_run_at v σ

/-- **The assembly stage of w4**: the same on the deployed (empty) storage. -/
theorem stage (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Main.evm4 Corpus.W4.code
      Verify.W4.scope :=
  (stageAt o).mono fun _ h => scopeAt_of_scope h

/-- The oracle of EthLib's call, as for w5 (SolidCore.Refinement.Solar.W1.oracle): one frame at
0x1000 called by 0x2000 (also the origin), in Target.blockEnv and Target.txEnv; every other
read is 0. w4 reads none of them, and every stage holds under every oracle. -/
def oracle : SolarTV.Machine.Oracle where
  env name _ _ :=
    if name = "caller" ∨ name = "origin" then BitVec.ofNat 256 callerAddress
    else if name = "address" then BitVec.ofNat 256 selfAddress
    else if name = "chainid" ∨ name = "number" ∨ name = "timestamp" then 1
    else if name = "gaslimit" then 30000000
    else 0
  result _ := 0
  storageAfter _ _ := 0
  transientAfter _ _ := 0
  keccak _ := 0
  caller := BitVec.ofNat 160 callerAddress

/-! ## The milestone -/

/-- **The w4 milestone.** solar's runtime bytecode for w4, which is the bytecode solar exported
with its stages (byte for byte, and as the hex its manifest records for -Ogas at osaka), meets
w4's specification verified on SolidCore, under EthLib on every call of set from the deployed
storage, through every stage of solar's pipeline: the source stage (lowering), the backend
(SolarTV.Milestone.W4.w4_mir_to_evmir) and the assembly stage (stage). -/
theorem certified :
    bytes = SolarTV.Export.Main.bytecode ∧
    SolarTV.Export.Main.Manifest.bytecodeHex = runtimeHex ∧
    SolarTV.Export.Main.Manifest.optimization = "Gas" ∧
    SolarTV.Export.Main.Manifest.evmVersion = "osaka" ∧
    Satisfies ethLib Corpus.W4.code Verify.W4.scope Verify.W4.pre Verify.W4.post := by
  refine ⟨bytes_exported, rfl, rfl, rfl, ?_⟩
  obtain ⟨c, hc, hspec⟩ := Verify.W4.satisfies
  exact bytecode_of_stages hspec (lowering oracle hc)
    ((SolarTV.Milestone.W4.w4_mir_to_evmir oracle).mono fun _ _ => trivial) (stage oracle)

/-- **The w4 milestone from any storage.** The same bytecode meets w4's specification from any
storage (Verify.W4.postAt: on every call of set with no value from any storage σ, v in slot 0
and every other slot of σ kept), under EthLib, through every stage of solar's pipeline, each
proved on every call from any storage. -/
theorem certifiedAt :
    Satisfies ethLib Corpus.W4.code Verify.W4.scopeAt Verify.W4.pre Verify.W4.postAt := by
  obtain ⟨c, hc, hspec⟩ := Verify.W4.satisfiesAt
  exact bytecode_of_stages hspec (loweringAt oracle hc)
    ((SolarTV.Milestone.W4.w4_mir_to_evmir oracle).mono fun _ _ => trivial) (stageAt oracle)

/-- info: 'SolidCore.Refinement.Solar.W4.target_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_run_at

/-- info: 'SolidCore.Refinement.Solar.W4.stageAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stageAt

/-- info: 'SolidCore.Refinement.Solar.W4.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified

/-- info: 'SolidCore.Refinement.Solar.W4.certifiedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifiedAt

end SolidCore.Refinement.Solar.W4
