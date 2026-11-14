import Contracts.CallFamilies.SkimRun
import Contracts.CallFamilies.SyncAgree
import SolarTV.MemorySymbolic

/-!
# skim in solar's MIR under the oracle hypothesis

mir_skim_agree: under CallsAgree o V, when SolidCore's run of skim(dst) in the world V asks V the
token's balanceOf(address(this)) (SyncAsk, the same call sync makes) and, when the balance read
returned a word at least the reserve, then asks V the token's transfer(dst, balance - reserve) with
the first exchange as history (PayAsk), solar's stage0 shows what SkimObs says: the bubbled revert,
the empty revert of a short return, the Panic(0x11) revert of the subtraction, the
Error("TRANSFER_FAILED") revert, the empty revert of a short or non-bool return word, or success with
the storage the transfer's answer leaves. Each call's agreement comes from CallsAgree, the second with
the first exchange as its history.
-/

namespace SolidCore.Refinement.CallFamilies.Skim

open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement
open EvmCompiler.Simulation
open SolidCore.Solidity.Source (addressToWord u256ToWord byteArrayToBytes)

set_option linter.deprecated false

/-- The 32 big-endian bytes of a word. -/
def wordBE (n : Nat) : List Nat := (List.range 32).map (fun i => n / 256 ^ (31 - i) % 256)

/-- The amount skim transfers: the balance word less the reserve, as the MIR subtracts. -/
def amtW (σ : List (Nat × Nat)) (a1 : CallResponse) : BitVec 256 :=
  Sync.retWord a1 - BitVec.ofNat 256 (slotValue σ 2)

/-- The input of transfer(dst, amount). -/
def transferInput (σ : List (Nat × Nat)) (dst : Nat) (a1 : CallResponse) : List Nat :=
  [169, 5, 156, 187] ++ wordBE dst ++ wordBE (amtW σ a1).toNat

/-- The second call SolidCore's skim asks V, after the balance read: pay's transfer. -/
structure PayAsk (σ : List (Nat × Nat)) (dst : Nat) (V : World)
    (world1 : SolidCore.Solidity.Shared.OpenWorld) (request1 : CallRequest) (a1 : CallResponse)
    (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) (a : CallResponse) : Prop where
  ans : V.ans [⟨.external world1 (.call request1), a1⟩] (.external world (.call request)) = some a
  kind : request.kind = .call
  callee : addressToWord request.codeAddress = slotValue σ 1 % 2 ^ 160
  value : u256ToWord request.transferValue = 0
  input : byteArrayToBytes request.calldata = transferInput σ dst a1
  storage : ∀ slot < 2 ^ 256, storageIn world slot = slotValue σ slot % 2 ^ 256
  transient : ∀ slot < 2 ^ 256, transientIn world slot = 0
  codes : ∀ x < 2 ^ 160, (codeIn world x).isEmpty = (codeIn a1.postWorld x).isEmpty
  size : a.returnData.size < 2 ^ 64

/-- The balance read ends skim before the transfer. -/
def Early (σ : List (Nat × Nat)) (a1 : CallResponse) : Prop :=
  a1.success = false ∨ a1.returnData.size < 32 ∨ (Sync.retWord a1).toNat < slotValue σ 2

def failObs (σ : List (Nat × Nat)) (data : List Nat) : Observable := ⟨false, data, [], slotValue σ⟩

/-- Panic(0x11). -/
def panicData : List Nat := [0x4e, 0x48, 0x7b, 0x71] ++ wordBE 17

/-- Error("TRANSFER_FAILED"). -/
def errData : List Nat := [0x08, 0xc3, 0x79, 0xa0] ++ wordBE 32 ++ wordBE 15 ++
  wordBE 38139611465464413496808033184516339178673403987523396430313160281336026497024

def obsEarly (σ : List (Nat × Nat)) (a1 : CallResponse) : Observable :=
  if a1.success then
    if a1.returnData.size < 32 then failObs σ [] else failObs σ panicData
  else failObs σ ((List.range a1.returnData.size).map (fun j => (a1.returnData.get! j).toNat))

def okObs (a : CallResponse) : Observable := ⟨true, [], [], fun slot => storageIn a.postWorld (slot % 2 ^ 256)⟩

def obsLate (σ : List (Nat × Nat)) (a : CallResponse) : Observable :=
  if a.success then
    if a.returnData.size = 0 then okObs a
    else if a.returnData.size < 32 then failObs σ []
    else if 1 < (Sync.retWord a).toNat then failObs σ []
    else if (Sync.retWord a).toNat = 0 then failObs σ errData
    else okObs a
  else failObs σ errData

/-- What SolidCore's skim(dst) in V shows, by the calls it asks. -/
def SkimObs (σ : List (Nat × Nat)) (dst : Nat) (V : World) (obs : Observable) : Prop :=
  ∃ world1 request1 a1, Sync.SyncAsk σ V world1 request1 a1 ∧ (Early σ a1 → obs = obsEarly σ a1) ∧
    (¬ Early σ a1 → ∃ world request a, PayAsk σ dst V world1 request1 a1 world request a ∧ obs = obsLate σ a)

theorem T_eq (o : Oracle) (σ : List (Nat × Nat)) (dst : Nat) : S7 o (S0' σ dst) = Sync.S4 o σ := rfl

theorem W1_eq (o : Oracle) (σ : List (Nat × Nat)) (dst : Nat) : W1 o (S0' σ dst) = Sync.W o σ := rfl



theorem bytes_store (m : Mem) (off : Nat) (v : BitVec 256) (i : Nat) :
    (m.store off v).bytes i = if off ≤ i ∧ i < off + 32 then Memory.byte v (i - off) else m.bytes i := by
  unfold Mem.store
  rw [Sync.bytes_expand]

theorem byte_toNat (v : BitVec 256) (k : Nat) (hk : k < 32) :
    (Memory.byte v k).toNat = v.toNat / 256 ^ (31 - k) % 256 := by
  unfold Memory.byte
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [show 2 ^ (8 * (31 - k)) = 256 ^ (31 - k) by rw [pow_mul]; norm_num]

theorem wordBytes_toNat (v : BitVec 256) : (Mem.wordBytes v).map BitVec.toNat = wordBE v.toNat := by
  unfold Mem.wordBytes wordBE
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact byte_toNat v i hi

theorem read_expand (m : Mem) (o z a b : Nat) : (m.expand o z).read a b = m.read a b := by
  simp only [Mem.read, Sync.bytes_expand]

/-- The last four bytes of the word stored at 0, as a revert from 28 reads them. -/
theorem read28 (m : Mem) (w : BitVec 256) :
    ((m.store 0 w).read 28 4).map BitVec.toNat =
      [w.toNat / 256 ^ 3 % 256, w.toNat / 256 ^ 2 % 256, w.toNat / 256 % 256, w.toNat % 256] := by
  simp only [Mem.read, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, bytes_store]
  simp [byte_toNat]

theorem read_split (m : Mem) (a k l n : Nat) (h : n = k + l) : m.read a n = m.read a k ++ m.read (a + k) l := by
  subst h; exact Mem.read_append m a k l

theorem err_data (s : State) : revertData (errHalt s).1 = errData := by
  simp only [errHalt, halt, if_true, revertData, read_expand]
  rw [show BitVec.toNat (28 : BitVec 256) = 28 from rfl, show BitVec.toNat (100 : BitVec 256) = 100 from rfl,
    read_split _ 28 4 96 100 rfl, read_split _ 32 32 64 96 rfl, read_split _ 64 32 32 64 rfl]
  simp only [List.map_append, read28]
  rw [Mem.read_store_disjoint _ 0 _ 32 32 (Or.inr (by norm_num)), Mem.read_store_disjoint _ 96 _ 32 32 (Or.inl (by norm_num)),
    Mem.read_store_disjoint _ 64 _ 32 32 (Or.inl (by norm_num)), Mem.read_store_same,
    Mem.read_store_disjoint _ 0 _ 64 32 (Or.inr (by norm_num)), Mem.read_store_disjoint _ 96 _ 64 32 (Or.inl (by norm_num)),
    Mem.read_store_same,
    Mem.read_store_disjoint _ 0 _ 96 32 (Or.inr (by norm_num)), Mem.read_store_same]
  simp only [wordBytes_toNat, errData, List.append_assoc]
  rfl

theorem panic_data (s : State) :
    revertData (halt { s with memory := (s.memory.store 32 17#256).store 0 0x4e487b71#256 } 28 36 true).1 = panicData := by
  simp only [halt, if_true, revertData, read_expand]
  rw [show BitVec.toNat (28 : BitVec 256) = 28 from rfl, show BitVec.toNat (36 : BitVec 256) = 36 from rfl,
    read_split _ 28 4 32 36 rfl]
  simp only [List.map_append, read28]
  rw [Mem.read_store_disjoint _ 0 _ 32 32 (Or.inr (by norm_num)), Mem.read_store_same]
  simp only [wordBytes_toNat, panicData]
  rfl

theorem in2_eq (m : Mem) (a b : BitVec 256) :
    (in2 m a b).map BitVec.toNat = [169, 5, 156, 187] ++ wordBE a.toNat ++ wordBE b.toNat := by
  simp only [in2, PM, read_expand]
  rw [read_split _ 160 4 64 68 rfl, read_split _ 164 32 32 64 rfl]
  rw [Mem.read_store_same, Mem.read_store_disjoint _ 196 _ 164 32 (Or.inl (by norm_num)), Mem.read_store_same,
    Mem.read_store_disjoint _ 196 _ 160 4 (Or.inl (by norm_num)), Mem.read_store_disjoint _ 164 _ 160 4 (Or.inl (by norm_num))]
  simp only [List.map_append, wordBytes_toNat, List.append_assoc]
  congr 1

theorem sem_skim (o : Oracle) (σ : List (Nat × Nat)) (dst : Nat) (hd : dst < 2 ^ 160)
    (hr : callFlag o (W1 o (S0' σ dst)) ≠ 0#256 →
      EvmRules.Evm.lt (o.env "returndatasize" (S7 o (S0' σ dst)).world []) 32#256 = 0#256 →
      EvmRules.Evm.lt ((S7 o (S0' σ dst)).memory.load 0) ((S7 o (S0' σ dst)).storage 2#256) = 0#256 →
      (rds2 o { S7 o (S0' σ dst) with memory := (S7 o (S0' σ dst)).memory.expand 0 32 } (BitVec.ofNat 256 dst)
        (EvmRules.Evm.sub ((S7 o (S0' σ dst)).memory.load 0) ((S7 o (S0' σ dst)).storage 2#256))).toNat < 2 ^ 64) :
    (moduleSem o).run SolarTV.Export.Calls.stage0 (skimCall σ dst) =
      some (observe (skimCall σ dst) (mirEnd o σ dst).2 (mirEnd o σ dst).1) := by
  show (moduleLayer.result o _ _).map _ = _
  rw [moduleLayer.result_of_ends (show moduleLayer.Ends o SolarTV.Export.Calls.stage0 (skimCall σ dst) (mirEnd o σ dst)
    from ⟨20, run_skim o σ dst hd hr⟩)]
  rfl

/-- The first call's agreement, with the code the second call sees. -/
theorem answer1 (o : Oracle) (V : World) (σ : List (Nat × Nat))
    (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) (a : CallResponse)
    (agree : CallsAgree o V) (hs : Sync.SyncAsk σ V world request a) :
    CodesAgree o (Sync.W o σ ++ [.read "gas"]) (codeIn a.postWorld) := by
  have hcalls : machineCalls (Sync.W o σ) =
      sourceCalls ([] ++ [⟨.external world (.call request), a⟩]) := by
    simp only [Sync.W, machineCalls, sourceCalls, List.nil_append, hs.kind, hs.callee, hs.value, hs.input,
      machineKind, List.getD]
    simp
  have hstore : ∀ slot < 2 ^ 256,
      ((State.initial (Sync.syncCall σ)).storage (BitVec.ofNat 256 slot)).toNat = storageIn world slot ∧
        ((fun _ => (0 : BitVec 256)) (BitVec.ofNat 256 slot)).toNat = transientIn world slot := by
    intro slot hslot
    refine ⟨?_, ?_⟩
    · rw [hs.storage slot hslot]
      simp only [State.initial, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hslot]
      rfl
    · rw [hs.transient slot hslot]; rfl
  have hcodes : CodesAgree o (Sync.W o σ).dropLast (codeIn world) := by
    intro x hx
    rw [hs.codes x hx]
    exact agree.codes [.read "gas"] rfl x hx
  obtain ⟨-, -, hrest⟩ := agree.calls [] world request a hs.ans (Sync.W o σ) .staticcall _ _ _ _
    rfl hcalls hstore hcodes
  obtain ⟨-, -, hc⟩ := hrest [.read "gas"] rfl
  intro x hx
  rw [hc x hx]
  rfl


/-- The second call's agreement: pay's CALL of transfer, with the balance read as its history. -/
theorem answer2 (o : Oracle) (V : World) (σ : List (Nat × Nat)) (dst : Nat) (hd : dst < 2 ^ 160)
    (world1 : SolidCore.Solidity.Shared.OpenWorld) (request1 : CallRequest) (a1 : CallResponse)
    (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) (a : CallResponse)
    (agree : CallsAgree o V) (hs : Sync.SyncAsk σ V world1 request1 a1)
    (hp : PayAsk σ dst V world1 request1 a1 world request a) (s : State)
    (hsw : s.world = Sync.W o σ) (hss : s.storage = (State.initial (Sync.syncCall σ)).storage)
    (hst : s.transient = fun _ => 0) (amt : BitVec 256) (hamt : amt = amtW σ a1) :
    ((callFlag o (W2 o s (BitVec.ofNat 256 dst) amt) = 1) ↔ a.success = true) ∧
      (∀ slot < 2 ^ 256, (o.storageAfter (W2 o s (BitVec.ofNat 256 dst) amt) (BitVec.ofNat 256 slot)).toNat =
        storageIn a.postWorld slot) ∧
      (rds2 o s (BitVec.ofNat 256 dst) amt).toNat = a.returnData.size ∧
      ∀ j < a.returnData.size,
        (returndataByte o (W2 o s (BitVec.ofNat 256 dst) amt) j).toNat = (a.returnData.get! j).toNat := by
  have hd' : dst < 2 ^ 256 := by omega
  have hin : (in2 s.memory (BitVec.ofNat 256 dst) amt).map BitVec.toNat = byteArrayToBytes request.calldata := by
    rw [in2_eq, hp.input, transferInput, hamt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd']
  have hcalls : machineCalls (W2 o s (BitVec.ofNat 256 dst) amt) =
      sourceCalls ([⟨.external world1 (.call request1), a1⟩] ++ [⟨.external world (.call request), a⟩]) := by
    simp only [W2, hsw, Sync.W, List.cons_append, List.nil_append, machineCalls, sourceCalls, hs.kind, hs.callee,
      hs.value, hs.input, hp.kind, hp.callee, hp.value, ← hin, machineKind, List.getD, hss]
    simp [State.initial, Sync.syncCall]
  have hstore : ∀ slot < 2 ^ 256,
      (s.storage (BitVec.ofNat 256 slot)).toNat = storageIn world slot ∧
        (s.transient (BitVec.ofNat 256 slot)).toNat = transientIn world slot := by
    intro slot hslot
    refine ⟨?_, ?_⟩
    · rw [hp.storage slot hslot, hss]
      simp only [State.initial, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hslot]
      rfl
    · rw [hp.transient slot hslot, hst]; rfl
  have hcodes : CodesAgree o (W2 o s (BitVec.ofNat 256 dst) amt).dropLast (codeIn world) := by
    have h1 := answer1 o V σ world1 request1 a1 agree hs
    have hdl : (W2 o s (BitVec.ofNat 256 dst) amt).dropLast = Sync.W o σ ++ [.read "gas"] := by
      simp [W2, hsw]
    rw [hdl]
    intro x hx
    rw [hp.codes x hx]
    exact h1 x hx
  obtain ⟨hflag, hsto, hrest⟩ := agree.calls [⟨.external world1 (.call request1), a1⟩] world request a hp.ans
    (W2 o s (BitVec.ofNat 256 dst) amt) .call _ _ _ _ (by simp [W2]; exact ⟨rfl, rfl⟩) hcalls hstore hcodes
  obtain ⟨hsz, hby, -⟩ := hrest [] rfl
  simp only [List.append_nil] at hsz hby
  have hsmall : a.returnData.size < 2 ^ 256 := lt_trans hp.size (by norm_num)
  refine ⟨hflag, fun slot hslot => (hsto (by rw [hp.kind]; decide) slot hslot).1, ?_, fun j hj => hby j hj (lt_trans hj hsmall)⟩
  rw [rds2, ← returndataSize, hsz, Nat.mod_eq_of_lt hsmall]


theorem obs_empty (call : Call) (s : State) :
    observe call (halt s 0 0 true).2 (halt s 0 0 true).1 = ⟨false, [], [], slotValue call.storage⟩ := by
  simp [halt, observe, Mem.read]

theorem obs_panic (call : Call) (s : State) :
    observe call (halt { s with memory := (s.memory.store 32 17#256).store 0 0x4e487b71#256 } 28 36 true).2
      (halt { s with memory := (s.memory.store 32 17#256).store 0 0x4e487b71#256 } 28 36 true).1 =
      ⟨false, panicData, [], slotValue call.storage⟩ := by
  have h := panic_data s
  simp only [halt, if_true, revertData] at h
  simp only [halt, if_true, observe, h]

theorem obs_err (call : Call) (s : State) :
    observe call (errHalt s).2 (errHalt s).1 = ⟨false, errData, [], slotValue call.storage⟩ := by
  have h := err_data s
  simp only [errHalt, halt, if_true, revertData] at h
  simp only [errHalt, halt, if_true, observe, h]

theorem obs_panic' (call : Call) (m : Mem) (st tr : BitVec 256 → BitVec 256) (w : List Event) :
    observe call (halt ⟨(m.store 32 17#256).store 0 0x4e487b71#256, st, tr, w⟩ 28 36 true).2
      (halt ⟨(m.store 32 17#256).store 0 0x4e487b71#256, st, tr, w⟩ 28 36 true).1 =
      ⟨false, panicData, [], slotValue call.storage⟩ :=
  obs_panic call ⟨m, st, tr, w⟩

theorem slt_small (a b : BitVec 256) (ha : a.toNat < 2 ^ 255) (hb : b.toNat < 2 ^ 255) :
    EvmRules.Evm.slt a b = EvmRules.Evm.lt a b := by
  have hma : a.msb = false := by rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega
  have hmb : b.msb = false := by rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega
  simp only [EvmRules.Evm.slt, EvmRules.Evm.lt, BitVec.slt_eq_ult, hma, hmb]
  simp

theorem load288 (o : Oracle) (s : State) (a b : BitVec 256) (a2 : CallResponse) (h32 : 32 ≤ a2.returnData.size)
    (hsz : (rds2 o s a b).toNat = a2.returnData.size)
    (hby : ∀ j < a2.returnData.size, (returndataByte o (W2 o s a b) j).toNat = (a2.returnData.get! j).toNat) :
    (((S8 o s a b).memory.expand 256 32).expand 256 32).load 288 = Sync.retWord a2 := by
  unfold Mem.load Mem.read Sync.retWord
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [Sync.bytes_expand, Sync.bytes_expand]
  simp only [S8]
  rw [Sync.bytes_write, if_pos (by rw [hsz]; omega)]
  apply BitVec.eq_of_toNat_eq
  rw [show 0 + (288 + i - 288) = i by omega, hby i (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]

theorem logs_S8 (o : Oracle) (s : State) (a b : BitVec 256) (m : Mem) (hw : s.world = Sync.W o σ) :
    logs { S8 o s a b with memory := m } = [] := by
  simp [logs, S8, W2, hw, Sync.W]

theorem storage_ok (o : Oracle) (W : List Event) (a2 : CallResponse)
    (hsto : ∀ slot < 2 ^ 256, (o.storageAfter W (BitVec.ofNat 256 slot)).toNat = storageIn a2.postWorld slot) :
    (fun slot => (o.storageAfter W (BitVec.ofNat 256 slot)).toNat) = fun slot => storageIn a2.postWorld (slot % 2 ^ 256) := by
  funext slot
  rw [← hsto (slot % 2 ^ 256) (Nat.mod_lt _ (by norm_num))]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp


/-- **skim's MIR under the oracle hypothesis.** -/
theorem mir_skim_agree (o : Oracle) (V : World) (σ : List (Nat × Nat)) (dst : Nat) (hd : dst < 2 ^ 160)
    (agree : CallsAgree o V) (obs : Observable) (h : SkimObs σ dst V obs) :
    (moduleSem o).run SolarTV.Export.Calls.stage0 (skimCall σ dst) = some obs := by
  obtain ⟨w1, r1, a1, hs1, hE, hL⟩ := h
  obtain ⟨hflag1, hsize1, hbytes1⟩ := Sync.answer o V σ w1 r1 a1 agree hs1
  have hlt := SolidCore.Refinement.Evm.Wide.slotValue_lt σ
  have hf0 : callFlag o (Sync.W o σ) = 0#256 ↔ a1.success = false := by
    constructor
    · intro h0
      cases hs : a1.success
      · rfl
      · have := hflag1.mpr hs; rw [h0] at this; exact absurd this (by decide)
    · intro hf
      rcases Sync.callFlag_cases o (Sync.W o σ) with h' | h'
      · exact h'
      · rw [hflag1.mp h'] at hf; cases hf
  have hsz1 : (o.env "returndatasize" (Sync.S4 o σ).world []).toNat = a1.returnData.size := hsize1
  have hlt1 : EvmRules.Evm.lt (o.env "returndatasize" (Sync.S4 o σ).world []) 32#256 = 0#256 ↔ ¬ a1.returnData.size < 32 := by
    rw [Sync.lt_word, hsz1]
    by_cases hc : a1.returnData.size < 32 <;> simp [hc]
  have hload1 : 32 ≤ a1.returnData.size → (Sync.M4 o σ).load 0 = Sync.retWord a1 := by
    intro hge
    unfold Mem.load Mem.read Sync.retWord
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have hmin : min 32 (returndataSize o (Sync.W o σ)).toNat = 32 := by rw [hsize1]; omega
    rw [Sync.M4, Sync.bytes_write, hmin]
    simp only [Nat.zero_le, Nat.zero_add, hi, and_self, if_true, Nat.sub_zero]
    apply BitVec.eq_of_toNat_eq
    rw [hbytes1 i (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]
  have hst2 : ((Sync.S4 o σ).storage 2#256).toNat = slotValue σ 2 := by
    show (BitVec.ofNat 256 (slotValue σ (2#256).toNat)).toNat = slotValue σ 2
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (hlt 2)
  have hlt2 : 32 ≤ a1.returnData.size →
      (EvmRules.Evm.lt ((Sync.S4 o σ).memory.load 0) ((Sync.S4 o σ).storage 2#256) = 0#256 ↔
        ¬ (Sync.retWord a1).toNat < slotValue σ 2) := by
    intro hge
    rw [Sync.lt_word, show (Sync.S4 o σ).memory = Sync.M4 o σ from rfl, hload1 hge, hst2]
    by_cases hc : (Sync.retWord a1).toNat < slotValue σ 2 <;> simp [hc]
  have hamt : 32 ≤ a1.returnData.size →
      EvmRules.Evm.sub ((Sync.S4 o σ).memory.load 0) ((Sync.S4 o σ).storage 2#256) = amtW σ a1 := by
    intro hge
    rw [show (Sync.S4 o σ).memory = Sync.M4 o σ from rfl, hload1 hge]
    rfl
  have late : ∀ (hsucc : a1.success = true) (hge : 32 ≤ a1.returnData.size)
      (hres : ¬ (Sync.retWord a1).toNat < slotValue σ 2), ¬ Early σ a1 := by
    intro hsucc hge hres he
    rcases he with he | he | he
    · rw [hsucc] at he; cases he
    · omega
    · exact hres he
  have hr : callFlag o (W1 o (S0' σ dst)) ≠ 0#256 →
      EvmRules.Evm.lt (o.env "returndatasize" (S7 o (S0' σ dst)).world []) 32#256 = 0#256 →
      EvmRules.Evm.lt ((S7 o (S0' σ dst)).memory.load 0) ((S7 o (S0' σ dst)).storage 2#256) = 0#256 →
      (rds2 o { S7 o (S0' σ dst) with memory := (S7 o (S0' σ dst)).memory.expand 0 32 } (BitVec.ofNat 256 dst)
        (EvmRules.Evm.sub ((S7 o (S0' σ dst)).memory.load 0) ((S7 o (S0' σ dst)).storage 2#256))).toNat < 2 ^ 64 := by
    rw [T_eq, W1_eq]
    intro c1 c2 c4
    have hsucc : a1.success = true := by
      cases hs : a1.success
      · exact absurd (hf0.mpr hs) c1
      · rfl
    have hge : 32 ≤ a1.returnData.size := by have := hlt1.mp c2; omega
    have hres := (hlt2 hge).mp c4
    obtain ⟨w2, r2, a2, hp, -⟩ := hL (late hsucc hge hres)
    obtain ⟨-, -, hsz2, -⟩ := answer2 o V σ dst hd w1 r1 a1 w2 r2 a2 agree hs1 hp
      { Sync.S4 o σ with memory := (Sync.S4 o σ).memory.expand 0 32 } rfl rfl rfl _ (hamt hge)
    rw [hsz2]; exact hp.size
  rw [sem_skim o σ dst hd hr]
  congr 1
  unfold mirEnd
  rw [T_eq, W1_eq]
  by_cases hsucc : a1.success = true
  swap
  · have hf : a1.success = false := by simpa using hsucc
    rw [if_pos (hf0.mpr hf), hE (Or.inl hf)]
    simp only [obsEarly, hsucc, if_false, failObs, halt, if_true, observe]
    congr 1
    rw [hsz1]
    unfold Mem.read
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp, Sync.bytes_expand, Sync.bytes_write, Nat.zero_le, Nat.zero_add]
    simp [hi]
    exact hbytes1 i hi
  have c1 : ¬ callFlag o (Sync.W o σ) = 0#256 := fun h0 => by rw [hf0.mp h0] at hsucc; cases hsucc
  rw [if_neg c1]
  by_cases hsmall : a1.returnData.size < 32
  · rw [if_neg (fun c => hlt1.mp c hsmall), hE (Or.inr (Or.inl hsmall))]
    simp only [obsEarly, hsucc, if_true, hsmall]
    rw [obs_empty]; rfl
  have hge : 32 ≤ a1.returnData.size := by omega
  rw [if_pos (hlt1.mpr hsmall)]
  by_cases hres : (Sync.retWord a1).toNat < slotValue σ 2
  · rw [if_neg (fun c => (hlt2 hge).mp c hres), hE (Or.inr (Or.inr hres))]
    simp only [obsEarly, hsucc, if_true, hsmall, if_false]
    rw [obs_panic']; rfl
  rw [if_pos ((hlt2 hge).mpr hres)]
  obtain ⟨w2, r2, a2, hp, hobs⟩ := hL (late hsucc hge hres)
  rw [hobs]
  obtain ⟨hflag2, hsto2, hsz2, hby2⟩ := answer2 o V σ dst hd w1 r1 a1 w2 r2 a2 agree hs1 hp
    { Sync.S4 o σ with memory := (Sync.S4 o σ).memory.expand 0 32 } rfl rfl rfl _ (hamt hge)
  by_cases hs2 : a2.success = true
  swap
  · have c5 : callFlag o (W2 o { Sync.S4 o σ with memory := (Sync.S4 o σ).memory.expand 0 32 } (BitVec.ofNat 256 dst)
        (EvmRules.Evm.sub ((Sync.S4 o σ).memory.load 0) ((Sync.S4 o σ).storage 2#256))) = 0#256 := by
      rcases Sync.callFlag_cases o (W2 o _ _ _) with h' | h'
      · exact h'
      · exact absurd (hflag2.mp h') hs2
    rw [if_pos c5]
    simp only [obsLate, hs2, if_false]
    rw [obs_err]; rfl
  have c5 : ¬ callFlag o (W2 o { Sync.S4 o σ with memory := (Sync.S4 o σ).memory.expand 0 32 } (BitVec.ofNat 256 dst)
      (EvmRules.Evm.sub ((Sync.S4 o σ).memory.load 0) ((Sync.S4 o σ).storage 2#256))) = 0#256 := by
    intro h0; have := hflag2.mpr hs2; rw [h0] at this; exact absurd this (by decide)
  rw [if_neg c5]
  have hsmall2 := hp.size
  have hok : ∀ m : Mem, observe (skimCall σ dst)
      { S8 o { Sync.S4 o σ with memory := (Sync.S4 o σ).memory.expand 0 32 } (BitVec.ofNat 256 dst)
          (EvmRules.Evm.sub ((Sync.S4 o σ).memory.load 0) ((Sync.S4 o σ).storage 2#256)) with memory := m } .stop =
        okObs a2 := by
    intro m
    simp only [observe, okObs]
    rw [logs_S8 (σ := σ) _ _ _ _ m rfl]
    congr 1
    exact storage_ok o _ a2 hsto2
  by_cases hz : a2.returnData.size = 0
  · have c6 : ¬ EvmRules.Evm.eq (rds2 o { Sync.S4 o σ with memory := (Sync.S4 o σ).memory.expand 0 32 }
        (BitVec.ofNat 256 dst) (EvmRules.Evm.sub ((Sync.S4 o σ).memory.load 0) ((Sync.S4 o σ).storage 2#256))) 0#256
        = 0#256 := by
      have h0 : rds2 o { Sync.S4 o σ with memory := (Sync.S4 o σ).memory.expand 0 32 } (BitVec.ofNat 256 dst)
          (EvmRules.Evm.sub ((Sync.S4 o σ).memory.load 0) ((Sync.S4 o σ).storage 2#256)) = 0#256 := by
        apply BitVec.eq_of_toNat_eq; rw [hsz2, hz]; rfl
      rw [h0, eq_self']; decide
    rw [if_neg c6]
    simp only [obsLate, hs2, if_true, hz]
    rw [hok]
  have c6 : EvmRules.Evm.eq (rds2 o { Sync.S4 o σ with memory := (Sync.S4 o σ).memory.expand 0 32 }
      (BitVec.ofNat 256 dst) (EvmRules.Evm.sub ((Sync.S4 o σ).memory.load 0) ((Sync.S4 o σ).storage 2#256))) 0#256
      = 0#256 := by
    simp only [EvmRules.Evm.eq]
    have : ¬ (rds2 o { Sync.S4 o σ with memory := (Sync.S4 o σ).memory.expand 0 32 } (BitVec.ofNat 256 dst)
        (EvmRules.Evm.sub ((Sync.S4 o σ).memory.load 0) ((Sync.S4 o σ).storage 2#256)) = 0#256) := by
      intro h0; apply hz; rw [← hsz2, h0]; rfl
    simp [this]
  rw [if_pos c6]
  have hslt : ∀ r : BitVec 256, r.toNat = a2.returnData.size →
      (EvmRules.Evm.slt r 32#256 = 0#256 ↔ ¬ a2.returnData.size < 32) := by
    intro r hr
    rw [slt_small r 32#256 (by omega) (by decide), Sync.lt_word, hr]
    by_cases hc : a2.returnData.size < 32 <;> simp [hc]
  by_cases hsm2 : a2.returnData.size < 32
  · rw [if_neg (fun c => (hslt _ hsz2).mp c hsm2)]
    simp only [obsLate, hs2, if_true, hz, if_false, hsm2]
    rw [obs_empty]; rfl
  rw [if_pos ((hslt _ hsz2).mpr hsm2)]
  have hl288 := load288 o { Sync.S4 o σ with memory := (Sync.S4 o σ).memory.expand 0 32 } (BitVec.ofNat 256 dst)
    (EvmRules.Evm.sub ((Sync.S4 o σ).memory.load 0) ((Sync.S4 o σ).storage 2#256)) a2 (by omega) hsz2 hby2
  simp only [hl288]
  by_cases hgt : 1 < (Sync.retWord a2).toNat
  · rw [if_neg (by simp [EvmRules.Evm.gt, BitVec.ult, hgt])]
    simp only [obsLate, hs2, if_true, hz, if_false, hsm2, hgt]
    rw [obs_empty]; rfl
  rw [if_pos (by simp [EvmRules.Evm.gt, BitVec.ult, hgt])]
  by_cases hz2 : (Sync.retWord a2).toNat = 0
  · have hw0 : Sync.retWord a2 = 0#256 := BitVec.eq_of_toNat_eq (by rw [hz2]; rfl)
    rw [if_pos (by rw [hw0]; exact ne_self' _)]
    simp only [obsLate, hs2, if_true, hz, if_false, hsm2, hgt, hz2]
    rw [obs_err]; rfl
  · have hw0 : Sync.retWord a2 ≠ 0#256 := fun h0 => hz2 (by rw [h0]; rfl)
    rw [if_neg (by simp [EvmRules.Evm.ne, hw0])]
    simp only [obsLate, hs2, if_true, hz, if_false, hsm2, hgt, hz2]
    rw [hok]

/-- info: 'SolidCore.Refinement.CallFamilies.Skim.mir_skim_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mir_skim_agree


/-- The source half of skim's stage in the world V from the storage σ, for the recipient dst:
SolidCore's run of skim(dst) asks V the calls SkimObs describes and shows what it says. -/
def SkimSource (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (V : World)
    (σ : List (Nat × Nat)) (dst : Nat) : Prop :=
  ∀ obs, Source.runIn V fuel c (skimCall σ dst) = some obs → SkimObs σ dst V obs

/-- **skim's source stage from its source half**, under every oracle that agrees with V. -/
theorem skim_stage (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (V : World)
    (scope : List (Nat × Nat) → Nat → Prop) (hscope : ∀ σ dst, scope σ dst → dst < 2 ^ 160)
    (src : ∀ σ dst, scope σ dst → SkimSource fuel c V σ dst)
    (o : Oracle) (agree : CallsAgree o V) :
    Stage (solidCoreIn V fuel) (moduleSem o) c SolarTV.Export.Calls.stage0
      (fun call => ∃ σ dst, scope σ dst ∧ call = skimCall σ dst) := by
  rintro call ⟨σ, dst, hσ, rfl⟩ obs hrun
  exact mir_skim_agree o V σ dst (hscope σ dst hσ) agree obs (src σ dst hσ obs hrun)

/-- info: 'SolidCore.Refinement.CallFamilies.Skim.skim_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms skim_stage

end SolidCore.Refinement.CallFamilies.Skim
