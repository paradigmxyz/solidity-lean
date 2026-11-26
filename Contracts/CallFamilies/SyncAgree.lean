import Contracts.CallFamilies.SyncMir
import SolidCore.Refinement.SourceOracle

/-!
# `sync` in solar's MIR under the oracle hypothesis

`mir_sync_agree`: under `CallsAgree o W`, when SolidCore's run of `sync()` in the world `W` asks
`W` the call `SyncAsk` describes (a `STATICCALL` of the token in slot 1 with solc's
`balanceOf(address(this))` input, from a world holding the call's storage) and `W` answers
`a`, solar's stage0 shows `obsOf σ a`: the callee's revert data when the call fails, an empty
revert when it returned fewer than 32 bytes, and otherwise the returned word in slot 2. This is the
MIR half of the source stage of `sync`, with the call's agreement (path induction for one call)
taken from `CallsAgree`.
-/

namespace SolidCore.Refinement.CallFamilies.Sync

open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement
open EvmCompiler.Simulation
open SolidCore.Solidity.Source (addressToWord u256ToWord byteArrayToBytes)

set_option linter.deprecated false

/-- The first 32 bytes of the return data as a big-endian word, as `MLOAD` reads them. -/
def retWord (a : CallResponse) : BitVec 256 :=
  ((List.range 32).map (fun i => BitVec.ofNat 8 (a.returnData.get! i).toNat)).foldl
    (fun acc b => (acc <<< 8) ||| b.setWidth 256) 0

/-- What `sync()` shows when the token answers `a`. -/
def obsOf (σ : List (Nat × Nat)) (a : CallResponse) : Observable :=
  if a.success then
    if a.returnData.size < 32 then ⟨false, [], [], slotValue σ⟩
    else ⟨true, [], [], fun slot =>
      (update (State.initial (syncCall σ)).storage 2 (retWord a) (BitVec.ofNat 256 slot)).toNat⟩
  else ⟨false, (List.range a.returnData.size).map (fun j => (a.returnData.get! j).toNat), [],
    slotValue σ⟩

/-- The call SolidCore's `sync()` asks `W`, with its answer. -/
structure SyncAsk (σ : List (Nat × Nat)) (V : World) (world : SolidCore.Solidity.Shared.OpenWorld)
    (request : CallRequest) (a : CallResponse) : Prop where
  ans : V.ans [] (.external world (.call request)) = some a
  kind : request.kind = .staticcall
  callee : addressToWord request.codeAddress = slotValue σ 1 % 2 ^ 160
  value : u256ToWord request.transferValue = 0
  input : byteArrayToBytes request.calldata = input.map BitVec.toNat
  storage : ∀ slot < 2 ^ 256, storageIn world slot = slotValue σ slot % 2 ^ 256
  transient : ∀ slot < 2 ^ 256, transientIn world slot = 0
  codes : ∀ x < 2 ^ 160, (codeIn world x).isEmpty =
    (SolidCore.Solidity.Shared.Account.codeAt (V.codes.getD []) x).isEmpty
  size : a.returnData.size < 2 ^ 256

theorem bytes_write (m : Mem) (off size : Nat) (src : Nat → Memory.Byte) (i : Nat) :
    (m.write off size src).bytes i = if off ≤ i ∧ i < off + size then src (i - off) else m.bytes i := by
  unfold Mem.write Mem.expand
  split <;> rfl

theorem bytes_expand (m : Mem) (off size i : Nat) : (m.expand off size).bytes i = m.bytes i := by
  unfold Mem.expand
  split <;> rfl

theorem lt_word (a b : BitVec 256) : EvmRules.Evm.lt a b = if a.toNat < b.toNat then 1 else 0 := by
  unfold EvmRules.Evm.lt
  by_cases h : a.toNat < b.toNat
  · have : a.ult b = true := by simp [BitVec.ult, h]
    simp [this, h]
  · have : a.ult b = false := by simp [BitVec.ult, h]
    simp [this, h]

/-- The world of one `STATICCALL` of the address in slot `i` with input `inp`, the first call of a
run from the storage `σ` (as `sync`'s and `feeOn`'s `W`). -/
def staticW (o : Oracle) (cd : ByteArray) (σ : List (Nat × Nat)) (i : Nat) (inp : List Memory.Byte) :
    List Event :=
  [.read "gas", .call .staticcall [o.env "gas" [.read "gas"] [], BitVec.ofNat 256 (slotValue σ i)] inp
    (State.initial { calldata := cd, callvalue := 0, storage := σ }).storage (fun _ => 0)]

/-- **The oracle's answer to a first `STATICCALL`**, from `CallsAgree` and the call SolidCore asks
(the fields of `SyncAsk`): its flag and return data, and the code a later call sees. -/
theorem static_answer (o : Oracle) (V : World) (σ : List (Nat × Nat)) (cd : ByteArray) (i : Nat)
    (inp : List Memory.Byte) (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest)
    (a : CallResponse) (agree : CallsAgree o V)
    (hans : V.ans [] (.external world (.call request)) = some a) (hkind : request.kind = .staticcall)
    (hcallee : addressToWord request.codeAddress = slotValue σ i % 2 ^ 160)
    (hvalue : u256ToWord request.transferValue = 0)
    (hinput : byteArrayToBytes request.calldata = inp.map BitVec.toNat)
    (hstorage : ∀ slot < 2 ^ 256, storageIn world slot = slotValue σ slot % 2 ^ 256)
    (htrans : ∀ slot < 2 ^ 256, transientIn world slot = 0)
    (hcodes : ∀ x < 2 ^ 160, (codeIn world x).isEmpty =
      (SolidCore.Solidity.Shared.Account.codeAt (V.codes.getD []) x).isEmpty)
    (hsize : a.returnData.size < 2 ^ 256) :
    ((callFlag o (staticW o cd σ i inp) = 1) ↔ a.success = true) ∧
      (returndataSize o (staticW o cd σ i inp)).toNat = a.returnData.size ∧
      (∀ j < a.returnData.size,
        (returndataByte o (staticW o cd σ i inp) j).toNat = (a.returnData.get! j).toNat) ∧
      CodesAgree o (staticW o cd σ i inp ++ [.read "gas"]) (codeIn a.postWorld) := by
  have hcalls : machineCalls (staticW o cd σ i inp) =
      sourceCalls ([] ++ [⟨.external world (.call request), a⟩]) := by
    simp only [staticW, machineCalls, sourceCalls, List.nil_append, hkind, hcallee, hvalue, hinput,
      machineKind, List.getD]
    simp
  have hstore : ∀ slot < 2 ^ 256,
      ((State.initial { calldata := cd, callvalue := 0, storage := σ }).storage
          (BitVec.ofNat 256 slot)).toNat = storageIn world slot ∧
        ((fun _ => (0 : BitVec 256)) (BitVec.ofNat 256 slot)).toNat = transientIn world slot := by
    intro slot hslot
    refine ⟨?_, by rw [htrans slot hslot]; rfl⟩
    rw [hstorage slot hslot]
    simp only [State.initial, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hslot]
  have hcodes' : CodesAgree o (staticW o cd σ i inp).dropLast (codeIn world) := by
    intro x hx
    rw [hcodes x hx]
    exact agree.codes [.read "gas"] rfl x hx
  obtain ⟨hflag, -, hrest⟩ := agree.calls [] world request a hans (staticW o cd σ i inp) .staticcall
    _ _ _ _ rfl hcalls hstore hcodes'
  obtain ⟨hsz, hby, -⟩ := hrest [] rfl
  obtain ⟨-, -, hc⟩ := hrest [.read "gas"] rfl
  simp only [List.append_nil] at hsz hby
  refine ⟨hflag, ?_, fun j hj => hby j hj (Nat.lt_trans hj hsize), fun x hx => ?_⟩
  · rw [hsz, Nat.mod_eq_of_lt hsize]
  · rw [hc x hx]; rfl

/-- The oracle's answer to sync's call, from `CallsAgree`. -/
theorem answer (o : Oracle) (V : World) (σ : List (Nat × Nat))
    (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) (a : CallResponse)
    (agree : CallsAgree o V) (hs : SyncAsk σ V world request a) :
    ((callFlag o (W o σ) = 1) ↔ a.success = true) ∧
      (returndataSize o (W o σ)).toNat = a.returnData.size ∧
      ∀ j < a.returnData.size, (returndataByte o (W o σ) j).toNat = (a.returnData.get! j).toNat := by
  obtain ⟨h1, h2, h3, -⟩ := static_answer o V σ (syncCall σ).calldata 1 input world request a agree
    hs.ans hs.kind hs.callee hs.value hs.input hs.storage hs.transient hs.codes hs.size
  exact ⟨h1, h2, h3⟩

theorem callFlag_cases (o : Oracle) (w : List Machine.Event) : callFlag o w = 0 ∨ callFlag o w = 1 := by
  unfold callFlag; split <;> simp

/-- A call's flag is zero exactly when it failed. -/
theorem flag_zero {o : Oracle} {w : List Machine.Event} {a : CallResponse}
    (hflag : callFlag o w = 1 ↔ a.success = true) : callFlag o w = 0 ↔ a.success = false := by
  rcases callFlag_cases o w with h | h <;> cases hs : a.success <;> simp_all

/-- The first word of the return data, as `MLOAD` reads it after the call copied it to 0. -/
theorem load_ret (o : Oracle) (w : List Machine.Event) (m : Mem) (a : CallResponse)
    (hsize : (returndataSize o w).toNat = a.returnData.size)
    (hbytes : ∀ j < a.returnData.size, (returndataByte o w j).toNat = (a.returnData.get! j).toNat)
    (h32 : 32 ≤ a.returnData.size) :
    (m.write 0 (min 32 (returndataSize o w).toNat) (returndataByte o w)).load 0 = retWord a := by
  unfold Mem.load Mem.read retWord
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [bytes_write, show min 32 (returndataSize o w).toNat = 32 by omega]
  simp only [Nat.zero_le, Nat.zero_add, hi, and_self, if_true, Nat.sub_zero]
  apply BitVec.eq_of_toNat_eq
  rw [hbytes i (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]

/-- A failed call's bubbled revert shows the callee's return data. -/
theorem obs_bubble (o : Oracle) (w : List Machine.Event) (call : Call) (s : State) (a : CallResponse)
    (hsize : (returndataSize o w).toNat = a.returnData.size)
    (hbytes : ∀ j < a.returnData.size, (returndataByte o w j).toNat = (a.returnData.get! j).toNat) :
    observe call
      (halt { s with memory := (s.memory.write 0 (returndataSize o w).toNat
        (fun i => returndataByte o w (0 + i))) } 0 (returndataSize o w) true).2
      (halt { s with memory := (s.memory.write 0 (returndataSize o w).toNat
        (fun i => returndataByte o w (0 + i))) } 0 (returndataSize o w) true).1 =
      ⟨false, (List.range a.returnData.size).map (fun j => (a.returnData.get! j).toNat), [],
        slotValue call.storage⟩ := by
  simp only [halt, if_true, observe]
  congr 1
  rw [hsize]
  unfold Mem.read
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp only [Function.comp, bytes_expand, bytes_write, Nat.zero_le, Nat.zero_add]
  simp [hi]
  exact hbytes i hi

/-- **sync's MIR under the oracle hypothesis.** -/
theorem mir_sync_agree (o : Oracle) (V : World) (σ : List (Nat × Nat))
    (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) (a : CallResponse)
    (agree : CallsAgree o V) (hs : SyncAsk σ V world request a) :
    (moduleSem o).run SolarTV.Export.Calls.stage0 (syncCall σ) = some (obsOf σ a) := by
  obtain ⟨hflag, hsize, hbytes⟩ := answer o V σ world request a agree hs
  rw [sem_sync]
  congr 1
  unfold mirEnd obsOf
  by_cases hsucc : a.success = true
  swap
  · rw [if_pos ((flag_zero hflag).mpr (by simpa using hsucc)), if_neg hsucc]
    exact obs_bubble o _ _ (S4 o σ) a hsize hbytes
  have hf : callFlag o (W o σ) ≠ 0 := fun h => by simp [(flag_zero hflag).mp h] at hsucc
  rw [if_neg hf, if_pos hsucc, lt_word, hsize]
  by_cases hlt : a.returnData.size < 32
  · have : ¬ ((if a.returnData.size < (32 : BitVec 256).toNat then (1 : BitVec 256) else 0) = 0) := by
      simp [hlt]
    rw [if_neg this, if_pos hlt]
    rfl
  · have : ((if a.returnData.size < (32 : BitVec 256).toNat then (1 : BitVec 256) else 0) = 0) := by
      simp [hlt]
    rw [if_pos this, if_neg hlt]
    have hload : (M4 o σ).load 0 = retWord a := load_ret o _ _ a hsize hbytes (by omega)
    simp only [observe, hload]
    rfl

/-- info: 'SolidCore.Refinement.CallFamilies.Sync.mir_sync_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mir_sync_agree

end SolidCore.Refinement.CallFamilies.Sync
