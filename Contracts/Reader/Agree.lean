import Contracts.Reader.Mir

/-!
# `read` in solar's MIR under the oracle hypothesis

`mir_read_agree`: under `CallsAgree o V`, when SolidCore's run of `read(a)` in the world `V` asks
`V` the call `ReadAsk` describes (a `STATICCALL` of `a` with `price()`'s input, from a world
holding the call's storage) and `V` answers `r`, solar's stage0 shows `obsOf σ a r`: the callee's
revert data when the call fails, an empty revert when it returned fewer than 32 bytes, the
`Panic(0x11)` revert when the returned word is the largest word, and otherwise the returned word
plus one.
-/

namespace SolidCore.Refinement.Reader

open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement
open EvmCompiler.Simulation
open SolidCore.Solidity.Source (addressToWord u256ToWord byteArrayToBytes)
open SolidCore.Refinement.CallFamilies

set_option linter.deprecated false

/-- The input of `price()`, as the MIR writes it. -/
def input : List Memory.Byte :=
  ((((Mem.initial.store 64 128).store 0 2687873534#256).expand 28 4).expand 0 32).read 28 4

theorem input_eq : input.map BitVec.toNat = [0xa0, 0x35, 0xb1, 0xfe] := by decide

/-- What `read` shows from the storage `σ` when its callee answers `r`, with `S` the storage
a successful call leaves. -/
def obsOfS (σ : List (Nat × Nat)) (r : CallResponse) (S : Nat → Nat) : Observable :=
  if r.success then
    if r.returnData.size < 32 then ⟨false, [], [], slotValue σ⟩
    else if (Sync.retWord r).toNat + 1 = 2 ^ 256 then ⟨false, Skim.panicData, [], slotValue σ⟩
    else ⟨true, Skim.wordBE ((Sync.retWord r).toNat + 1), [], S⟩
  else ⟨false, (List.range r.returnData.size).map (fun j => (r.returnData.get! j).toNat), [],
    slotValue σ⟩

/-- What `read(a)` shows when `a` answers `r`: a successful call leaves the storage it started
with. -/
def obsOf (σ : List (Nat × Nat)) (a : Nat) (r : CallResponse) : Observable :=
  obsOfS σ r (storageOf (State.initial (readCall σ a)))

/-- The call SolidCore's `read(a)` asks `V`, with its answer. -/
structure ReadAsk (σ : List (Nat × Nat)) (a : Nat) (V : World) (world : SolidCore.Solidity.Shared.OpenWorld)
    (request : CallRequest) (r : CallResponse) : Prop where
  ans : V.ans [] (.external world (.call request)) = some r
  kind : request.kind = .staticcall
  callee : addressToWord request.codeAddress = a
  value : u256ToWord request.transferValue = 0
  input : byteArrayToBytes request.calldata = input.map BitVec.toNat
  storage : ∀ slot < 2 ^ 256, storageIn world slot = slotValue σ slot % 2 ^ 256
  transient : ∀ slot < 2 ^ 256, transientIn world slot = 0
  codes : ∀ x < 2 ^ 160, (codeIn world x).isEmpty =
    (SolidCore.Solidity.Shared.Account.codeAt (V.codes.getD []) x).isEmpty
  size : r.returnData.size < 2 ^ 256

theorem mem7_S0 (σ : List (Nat × Nat)) (a : Nat) :
    ((((mem7 (S0 σ a)).expand 28 4).expand 0 32).read 28 4) = input := rfl

/-- **The oracle's answer to read's call**, from `CallsAgree`. -/
theorem answer (o : Oracle) (V : World) (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 160)
    (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) (r : CallResponse)
    (agree : CallsAgree o V) (hs : ReadAsk σ a V world request r) :
    ((callFlag o (W1 o (S0 σ a) a) = 1) ↔ r.success = true) ∧
      (returndataSize o (W1 o (S0 σ a) a)).toNat = r.returnData.size ∧
      ∀ j < r.returnData.size, (returndataByte o (W1 o (S0 σ a) a) j).toNat = (r.returnData.get! j).toNat := by
  have hcalls : machineCalls (W1 o (S0 σ a) a) =
      sourceCalls ([] ++ [⟨.external world (.call request), r⟩]) := by
    have hm : machineCalls (W1 o (S0 σ a) a) =
        [(.staticcall, (BitVec.ofNat 256 a).toNat % 2 ^ 160, 0, input.map BitVec.toNat)] := rfl
    rw [hm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans ha (by decide : (2:Nat) ^ 160 < 2 ^ 256)),
      Nat.mod_eq_of_lt ha]
    simp only [sourceCalls, List.nil_append, hs.kind, hs.callee, hs.value, hs.input, machineKind]
  have hstore : ∀ slot < 2 ^ 256,
      ((S0 σ a).storage (BitVec.ofNat 256 slot)).toNat = storageIn world slot ∧
        ((S0 σ a).transient (BitVec.ofNat 256 slot)).toNat = transientIn world slot := by
    intro slot hslot
    refine ⟨?_, by rw [hs.transient slot hslot]; rfl⟩
    rw [hs.storage slot hslot]
    simp only [S0, State.initial, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hslot]
    rfl
  have hcodes' : CodesAgree o (W1 o (S0 σ a) a).dropLast (codeIn world) := by
    intro x hx
    rw [hs.codes x hx]
    exact agree.codes [.read "gas"] rfl x hx
  obtain ⟨hflag, -, hrest⟩ := agree.calls [] world request r hs.ans (W1 o (S0 σ a) a) .staticcall
    _ _ _ _ rfl hcalls hstore hcodes'
  obtain ⟨hsz, hby, -⟩ := hrest [] rfl
  simp only [List.append_nil] at hsz hby
  refine ⟨hflag, ?_, fun j hj => hby j hj (Nat.lt_trans hj hs.size)⟩
  rw [hsz, Nat.mod_eq_of_lt hs.size]

theorem T_mem (o : Oracle) (σ : List (Nat × Nat)) (a : Nat) :
    (T o σ a).memory = (((mem7 (S0 σ a)).expand 28 4).expand 0 32).write 0
      (min 32 (returndataSize o (W1 o (S0 σ a) a)).toNat) (returndataByte o (W1 o (S0 σ a) a)) := rfl

theorem T_world (o : Oracle) (σ : List (Nat × Nat)) (a : Nat) : (T o σ a).world = W1 o (S0 σ a) a := rfl

theorem T_storage (o : Oracle) (σ : List (Nat × Nat)) (a : Nat) :
    (T o σ a).storage = (State.initial (readCall σ a)).storage := rfl

theorem logs_T4 (o : Oracle) (σ : List (Nat × Nat)) (a : Nat) (m : Mem) :
    logs { T4 o σ a with memory := m } = [] := by
  simp [logs, T4, T_world, W1, S0, State.initial]

/-- **read's MIR under the oracle hypothesis.** -/
theorem mir_read_agree (o : Oracle) (V : World) (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 160)
    (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) (r : CallResponse)
    (agree : CallsAgree o V) (hs : ReadAsk σ a V world request r) :
    (moduleSem o).run SolarTV.Export.Reader.stage0 (readCall σ a) = some (obsOf σ a r) := by
  obtain ⟨hflag, hsize, hbytes⟩ := answer o V σ a ha world request r agree hs
  rw [sem_read o σ a ha]
  congr 1
  unfold mirEnd obsOf obsOfS
  by_cases hsucc : r.success = true
  swap
  · rw [if_pos (show callFlag o (W1 o (S0 σ a) a) = 0#256 from (Sync.flag_zero hflag).mpr (by simpa using hsucc)),
      if_neg hsucc]
    exact Sync.obs_bubble o _ _ (T o σ a) r hsize hbytes
  have hf : callFlag o (W1 o (S0 σ a) a) ≠ 0#256 := fun h => by simp [(Sync.flag_zero hflag).mp h] at hsucc
  rw [if_neg hf, if_pos hsucc]
  rw [T_world, show o.env "returndatasize" (W1 o (S0 σ a) a) [] = returndataSize o (W1 o (S0 σ a) a) from rfl,
    Sync.lt_word, hsize]
  by_cases hlt : r.returnData.size < 32
  · have : ¬ ((if r.returnData.size < (32#256).toNat then (1 : BitVec 256) else 0) = 0#256) := by
      simp [hlt]
    rw [if_neg this, if_pos hlt]
    rfl
  have : ((if r.returnData.size < (32#256).toNat then (1 : BitVec 256) else 0) = 0#256) := by
    simp [hlt]
  rw [if_pos this, if_neg hlt]
  have hload : (T o σ a).memory.load 0 = Sync.retWord r := by
    rw [T_mem]; exact Sync.load_ret o _ _ r hsize hbytes (by omega)
  have hinc : inc o σ a = Sync.retWord r + 1#256 := by rw [inc, hload]
  have hrw := (Sync.retWord r).isLt
  by_cases hov : (Sync.retWord r).toNat + 1 = 2 ^ 256
  · have he : EvmRules.Evm.eq (inc o σ a) 0#256 ≠ 0#256 := by
      have h0 : inc o σ a = 0#256 := by
        rw [hinc]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]; simp [hov]
      simp [EvmRules.Evm.eq, h0]
    rw [if_neg he, if_pos hov]
    have hp := Skim.panic_data (T4 o σ a)
    simp only [halt, if_true, revertData] at hp
    simp only [halt, if_true, observe, hp]
    rfl
  · have hn : (inc o σ a).toNat = (Sync.retWord r).toNat + 1 := by
      rw [hinc, BitVec.toNat_add]; simp; omega
    have he : EvmRules.Evm.eq (inc o σ a) 0#256 = 0#256 := by
      have h0 : inc o σ a ≠ 0#256 := fun h => by rw [h] at hn; simp at hn
      simp [EvmRules.Evm.eq, h0]
    rw [if_pos he, if_neg hov]
    simp only [halt, Bool.false_eq_true, if_false, observe]
    congr 1
    · rw [Skim.read_expand]
      rw [show BitVec.toNat (0 : BitVec 256) = 0 from rfl, show BitVec.toNat (32 : BitVec 256) = 32 from rfl,
        Mem.read_store_same, Skim.wordBytes_toNat, hn]

/-- info: 'SolidCore.Refinement.Reader.mir_read_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mir_read_agree

end SolidCore.Refinement.Reader
