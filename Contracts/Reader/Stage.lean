import Contracts.Reader.SourceRun
import Contracts.Reader.Facts
import SolidCore.Refinement.Solar.AssembleCallWorld
import SolarTV.Composition

/-!
# Reader's SolidCore source stage in every open world

`reader_stage`: SolidCore's checked `Reader` (type checked from `Certified/reader/reader.sol`'s
solc AST by the kernel) refines solar's first lowered MIR on every valid call of `read(address)`,
in every open world whose seeded code is at addresses below `2 ^ 160` and whose static calls to
code answer return data shorter than `2 ^ 256` bytes, under every MIR oracle that agrees with the
world (`CallsAgree`); and SolidCore's run of every valid call is total there. A precompile callee
needs no size premise: an open world answers it as SolidCore's precompile on `price()`'s four
input bytes, whose output is at most 32 bytes (`pre_size`).
-/

namespace SolidCore.Refinement.Reader

open SolarTV SolidCore.Refinement SolidCore.Refinement.Solar
open SolidCore.Solidity.Source EvmCompiler.Simulation
open SolidCore.Solidity.Shared.Precompile (Kind kindOfAddress? execute? modexpMinimumGas)

/-- `price()`'s input bytes. -/
abbrev priceInput : List Nat := [0xa0, 0x35, 0xb1, 0xfe]

theorem exec_ecrecover : (execute? .ecrecover priceInput).map (fun p => p.2.length) = some 0 := by decide +kernel
theorem exec_sha256 : (execute? .sha256 priceInput).map (fun p => p.2.length) = some 32 := by decide +kernel
theorem exec_ripemd160 : (execute? .ripemd160 priceInput).map (fun p => p.2.length) = some 32 := by decide +kernel
theorem exec_identity : (execute? .identity priceInput).map (fun p => p.2.length) = some 4 := by decide +kernel
theorem exec_modexp : execute? .modexp priceInput = none := by decide +kernel
theorem exec_bnAdd : (execute? .bnAdd priceInput).map (fun p => p.2.length) = some 0 := by decide +kernel
theorem exec_bnMul : (execute? .bnMul priceInput).map (fun p => p.2.length) = some 0 := by decide +kernel
theorem exec_bnPairing : (execute? .bnPairing priceInput).map (fun p => p.2.length) = some 0 := by decide +kernel
theorem exec_blake2f : (execute? .blake2f priceInput).map (fun p => p.2.length) = some 0 := by decide +kernel
theorem exec_pointEvaluation : (execute? .pointEvaluation priceInput).map (fun p => p.2.length) = some 0 := by
  decide +kernel
theorem modexp_gas : 2 ^ 256 ≤ modexpMinimumGas priceInput := by decide +kernel

theorem u256_lt (g : EvmYul.UInt256) : u256ToWord g < 2 ^ 256 := g.val.isLt

theorem exec_some : ∀ k : Kind, k ≠ .modexp → ∃ p, execute? k priceInput = some p ∧ p.2.length ≤ 32 := by
  intro k hk
  cases k
  · obtain ⟨p, hp, hl⟩ := Option.map_eq_some_iff.mp exec_ecrecover; exact ⟨p, hp, by omega⟩
  · obtain ⟨p, hp, hl⟩ := Option.map_eq_some_iff.mp exec_sha256; exact ⟨p, hp, by omega⟩
  · obtain ⟨p, hp, hl⟩ := Option.map_eq_some_iff.mp exec_ripemd160; exact ⟨p, hp, by omega⟩
  · obtain ⟨p, hp, hl⟩ := Option.map_eq_some_iff.mp exec_identity; exact ⟨p, hp, by omega⟩
  · exact absurd rfl hk
  · obtain ⟨p, hp, hl⟩ := Option.map_eq_some_iff.mp exec_bnAdd; exact ⟨p, hp, by omega⟩
  · obtain ⟨p, hp, hl⟩ := Option.map_eq_some_iff.mp exec_bnMul; exact ⟨p, hp, by omega⟩
  · obtain ⟨p, hp, hl⟩ := Option.map_eq_some_iff.mp exec_bnPairing; exact ⟨p, hp, by omega⟩
  · obtain ⟨p, hp, hl⟩ := Option.map_eq_some_iff.mp exec_blake2f; exact ⟨p, hp, by omega⟩
  · obtain ⟨p, hp, hl⟩ := Option.map_eq_some_iff.mp exec_pointEvaluation; exact ⟨p, hp, by omega⟩

/-- **A precompile's answer to `price()`**: SolidCore answers a `STATICCALL` with no value of
`price()`'s input to a precompile address, with return data of at most 32 bytes. -/
theorem pre_answer (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest)
    (hk : request.kind = .staticcall) (hv : u256ToWord request.transferValue = 0)
    (hin : byteArrayToBytes request.calldata = priceInput) (kind : Kind)
    (hpre : kindOfAddress? (addressToWord request.codeAddress) = some kind) :
    ∃ r, precompileAnswerCall? world request = some r ∧ r.returnData.size < 2 ^ 256 := by
  unfold precompileAnswerCall?
  rw [hk]
  simp only [hv, beq_self_eq_true, if_true, hpre, hin]
  by_cases hm : kind = .modexp
  · subst hm
    rw [exec_modexp]
    have hg : u256ToWord request.requestedGas < modexpMinimumGas priceInput :=
      lt_of_lt_of_le (u256_lt _) modexp_gas
    simp only [beq_self_eq_true, Bool.true_and, decide_eq_true hg, if_true]
    exact ⟨_, rfl, by simp⟩
  · obtain ⟨⟨b, out⟩, hp, hl⟩ := exec_some kind hm
    rw [hp]
    refine ⟨_, rfl, ?_⟩
    simp only [bytesToByteArray, ByteArray.size, List.size_toArray, List.length_map, Array.size]
    simp only at hl
    omega

/-- The calls of `read(address)` with a clean address argument that is not the contract itself
(no reentrant call into itself), no value, from any storage. -/
def ReadValid (call : Call) : Prop :=
  ∃ a σ, a < 2 ^ 160 ∧ a ≠ selfAddress ∧
    call = { calldata := Abi.calldata 0xa087a87e [a], callvalue := 0, storage := σ }

/-- The answers to `read`'s call are shorter than `2 ^ 256` bytes in an open world whose static
calls to code are. -/
theorem answer_size (V : World) (hopen : V.Open)
    (hsize : ∀ h world request a, V.ans h (.external world (.call request)) = some a →
      Witness.toCode (machineKind request.kind) (addressToWord request.codeAddress)
        (u256ToWord request.transferValue) = true →
      a.returnData.size < 2 ^ 256) (a : Nat) :
    ∀ world request r, V.ans [] (.external world (.call request)) = some r →
      request.kind = .staticcall → addressToWord request.codeAddress = a →
      u256ToWord request.transferValue = 0 → byteArrayToBytes request.calldata = [0xa0, 0x35, 0xb1, 0xfe] →
      r.returnData.size < 2 ^ 256 := by
  intro world request r hans hk _ hv hin
  cases hpre : kindOfAddress? (addressToWord request.codeAddress) with
  | none =>
    apply hsize [] world request r hans
    simp [Witness.toCode, Witness.prePath, Witness.isStaticM, hk, machineKind, hpre]
  | some kind =>
    obtain ⟨r', hr', hs'⟩ := pre_answer world request hk hv hin kind hpre
    have h := hopen.precompiles [] world request r' hr'
    rw [hans] at h
    cases h
    exact hs'

/-- After `read`'s static call the answered world holds the storage the call started with. -/
theorem post_storage {o : Machine.Oracle} {V : World} (agree : CallsAgree o V) {σ : List (Nat × Nat)} {a : Nat}
    {world : SolidCore.Solidity.Shared.OpenWorld} {request : CallRequest} {r : CallResponse}
    (hask : ReadAsk σ a V world request r) :
    (fun slot => storageIn r.postWorld slot) = Machine.storageOf (Machine.State.initial (readCall σ a)) := by
  funext slot
  rw [← storageIn_mod, (agree.static [] world request r hask.ans hask.kind _).1,
    hask.storage _ (Nat.mod_lt _ (by decide))]
  simp [Machine.storageOf, Machine.State.initial, readCall, BitVec.toNat_ofNat]

/-- **Reader's SolidCore source stage and totality in every open world.** SolidCore's checked
`Reader` (`contract?`, the kernel's type check of `Certified/reader/reader.sol`'s solc AST) runs
every valid call of `read(address)` as solar's first lowered MIR does under every oracle that
agrees with the world, and runs every valid call to an end, in every open world whose seeded code
is at addresses below `2 ^ 160` and whose static calls to code answer return data shorter than
`2 ^ 256` bytes. -/
theorem reader_stage : ∃ c, SolidCore.Verify.VC.Reader.contract? = .ok c ∧
    (∀ V : World, V.Open → (∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160) →
      (∀ h world request a, V.ans h (.external world (.call request)) = some a →
        Witness.toCode (machineKind request.kind) (addressToWord request.codeAddress)
          (u256ToWord request.transferValue) = true →
        a.returnData.size < 2 ^ 256) →
      ∀ o, CallsAgree o V →
        Stage (solidCoreIn V SolidCore.Verify.VC.Reader.fuel) (mirSem o) c SolarTV.Export.Reader.stage0 ReadValid) ∧
    (∀ V : World, V.Open → (∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160) →
      (∀ h world request a, V.ans h (.external world (.call request)) = some a →
        Witness.toCode (machineKind request.kind) (addressToWord request.codeAddress)
          (u256ToWord request.transferValue) = true →
        a.returnData.size < 2 ^ 256) →
      ∀ call, ReadValid call → (Source.runIn V SolidCore.Verify.VC.Reader.fuel c call).isSome) := by
  obtain ⟨c, hc, hfind, hfields, hb, hh, hcc, d, hd, hdt, hde⟩ := reader_facts
  have run : ∀ V : World, V.Open → (∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160) →
      (∀ h world request a, V.ans h (.external world (.call request)) = some a →
        Witness.toCode (machineKind request.kind) (addressToWord request.codeAddress)
          (u256ToWord request.transferValue) = true →
        a.returnData.size < 2 ^ 256) →
      ∀ σ a, a < 2 ^ 160 → a ≠ selfAddress →
      ∃ world request r, ReadAsk σ a V world request r ∧
        Source.runIn V SolidCore.Verify.VC.Reader.fuel c (readCall σ a) =
          some (obsOfS σ r (fun slot => storageIn r.postWorld slot)) :=
    fun V hopen hkeys hsize σ a ha hself =>
      read_source 4091 V hd hfind hfields hdt hde hb hh hcc hkeys σ a ha hself (hopen.calls [])
        (answer_size V hopen hsize a)
  refine ⟨c, hc, ?_, ?_⟩
  · intro V hopen hkeys hsize o agree
    rintro call ⟨a, σ, ha, hself, rfl⟩ obs hrun
    obtain ⟨world, request, r, hask, hrun'⟩ := run V hopen hkeys hsize σ a ha hself
    change Source.runIn V SolidCore.Verify.VC.Reader.fuel c (readCall σ a) = some obs at hrun
    rw [hrun'] at hrun
    cases hrun
    change (MIR.Lowered.moduleSem o).run SolarTV.Export.Reader.stage0 (readCall σ a) = _
    rw [post_storage agree hask]
    exact mir_read_agree o V σ a ha world request r agree hask
  · intro V hopen hkeys hsize
    rintro call ⟨a, σ, ha, hself, rfl⟩
    obtain ⟨world, request, r, -, hrun'⟩ := run V hopen hkeys hsize σ a ha hself
    change (Source.runIn V SolidCore.Verify.VC.Reader.fuel c (readCall σ a)).isSome = true
    rw [hrun']
    rfl

/-- info: 'SolidCore.Refinement.Reader.reader_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reader_stage

end SolidCore.Refinement.Reader
