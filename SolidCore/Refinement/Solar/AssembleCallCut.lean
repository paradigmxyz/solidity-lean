import SolidCore.Refinement.Solar.AssembleCall
import SolidCore.Refinement.Solar.AssembleCallWorld
import SolidCore.Refinement.Solar.AssembleCallPre
import EthLib.Base.Proofs.U256

/-!
# A STATICCALL to code as a cut of a run, at the frame's own gas

`staticcall_cut` is the step the checker's segments (`AssembleCut.seg`) take at a STATICCALL to
code: from a run of the bytecode that succeeds, the STATICCALL had the gas for its access and memory
(`AssembleCall.staticcall_back`, EIP-150 forwarding), and the run goes on from the frame after it,
with the callee frame's flag and output. The run's table grows by that flag and output
(`RunTable.oks`, `RunTable.outs`), and under the oracle of every extension of it
(`AssembleCallWorld.OS`) SolarTV's STATICCALL pushes the same flag, leaves the same return data and
memory, and keeps storage and logs as EthLib's frame does: the relation of a block entry holds again.

The same cut covers a STATICCALL to ECRECOVER (address 1) under `PreOk`: there the oracle answers
as the source does (SolidCore's precompile semantics, `tabResp` falls back to `failResp`), and
`AssembleCallPre.ecrecover_answer` shows EthLib's callee frame gives that flag and output, under
the named `AssembleCallPre.EcrecoverAgree`. The table still grows by one entry per STATICCALL.

The runner of messages must meet `StaticOk`: `StaticKept`, proved of EthLib's runner
(`AssembleCall.meets_static`), and two named hypotheses that a final theorem using this cut lists:
`StaticNoLogs` (EIP-214: a static message that succeeds ends with no log; EthLib's LOG fails in a
static frame, but EthLib proves only that a static message keeps the state,
`processMessage_sameOutside_static`, not its logs) and `OutputFits` (a callee's output is shorter
than `2 ^ 256` bytes, which the gas paid for its memory bounds but which is not derived here).
-/

namespace SolidCore.Refinement.Solar.AssembleCallCut

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Witness
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleCut SolidCore.Refinement.Solar.AssembleEffects
open SolidCore.Refinement.Solar.AssembleLoop SolidCore.Refinement.Solar.AssembleRun
open SolidCore.Refinement.Solar.AssembleCall SolidCore.Refinement.Solar.AssembleCallWorld
open SolidCore.Refinement.Solar.AssembleDyn
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-! ## Memory a run pays for, over several ranges -/

/-- Growing memory of whole words for a list of ranges costs the price of the grown memory less the
price of the old one, keeps whole words, and covers every nonempty range. -/
theorem extendMemory_facts : ∀ (l : List (U256 × U256)) (size : Nat), size % 32 = 0 →
    (extendMemory size l).cost + memoryGasCost size =
        memoryGasCost (size + (extendMemory size l).expandBy) ∧
      (size + (extendMemory size l).expandBy) % 32 = 0 ∧
      ∀ r ∈ l, r.2 ≠ 0 → r.1.toNat + r.2.toNat ≤ size + (extendMemory size l).expandBy
  | [], size, hmod => by simp [extendMemory, hmod]
  | (o, sz) :: l, size, hmod => by
    have ih := extendMemory_facts l
    by_cases hz : sz = 0
    · obtain ⟨h1, h2, h3⟩ := ih size hmod
      simp only [extendMemory, hz, ite_true]
      refine ⟨h1, h2, fun r hr hr0 => ?_⟩
      rcases List.mem_cons.1 hr with rfl | hr
      · exact absurd rfl hr0
      · exact h3 r hr hr0
    · have hc := ceil32_of_mod hmod
      by_cases hle : ceil32 (o.toNat + sz.toNat) ≤ ceil32 size
      · obtain ⟨h1, h2, h3⟩ := ih size hmod
        simp only [extendMemory, hz, ite_false, hle, ite_true]
        refine ⟨h1, h2, fun r hr hr0 => ?_⟩
        rcases List.mem_cons.1 hr with rfl | hr
        · have := le_ceil32 (o.toNat + sz.toNat)
          dsimp only
          omega
        · exact h3 r hr hr0
      · obtain ⟨h1, h2, h3⟩ := ih (ceil32 (o.toNat + sz.toNat)) (ceil32_mod _)
        simp only [extendMemory, hz, ite_false, hle]
        have hlt : size < ceil32 (o.toNat + sz.toNat) := by omega
        have hm := memoryGasCost_mono (Nat.le_of_lt hlt)
        rw [hc]
        have he : size + (ceil32 (o.toNat + sz.toNat) - size +
            (extendMemory (ceil32 (o.toNat + sz.toNat)) l).expandBy) =
            ceil32 (o.toNat + sz.toNat) + (extendMemory (ceil32 (o.toNat + sz.toNat)) l).expandBy := by
          omega
        rw [he]
        refine ⟨by omega, h2, fun r hr hr0 => ?_⟩
        rcases List.mem_cons.1 hr with rfl | hr
        · have := le_ceil32 (o.toNat + sz.toNat)
          dsimp only
          omega
        · exact h3 r hr hr0

/-- **A paid growth of memory for two ranges keeps the budget**: each nonempty range's words are
within SolarTV's count, and the grown memory's price and the gas left are within the budget. -/
theorem budget_grow2 {size g G pre : Nat} (hmod : size % 32 = 0) {o1 s1 o2 s2 : U256}
    (hb : memoryGasCost size + g ≤ G) (hG : G < 2 ^ 300)
    (hg : pre + (extendMemory size [(o1, s1), (o2, s2)]).cost ≤ g) :
    (s1 = 0 ∨ (o1.toNat + s1.toNat + 31) / 32 < 2 ^ 251) ∧
      (s2 = 0 ∨ (o2.toNat + s2.toNat + 31) / 32 < 2 ^ 251) ∧
      memoryGasCost (size + (extendMemory size [(o1, s1), (o2, s2)]).expandBy) +
        (g - (pre + (extendMemory size [(o1, s1), (o2, s2)]).cost)) ≤ G ∧
      (s2 ≠ 0 → o2.toNat + s2.toNat ≤ size + (extendMemory size [(o1, s1), (o2, s2)]).expandBy) := by
  obtain ⟨h1, -, h3⟩ := extendMemory_facts [(o1, s1), (o2, s2)] size hmod
  have hw : ∀ r ∈ [(o1, s1), (o2, s2)], r.2 = 0 ∨ (r.1.toNat + r.2.toNat + 31) / 32 < 2 ^ 251 := by
    intro r hr
    by_cases hz : r.2 = 0
    · exact .inl hz
    · refine .inr (words_lt_of_cost (B := G) ?_ hG)
      have := memoryGasCost_mono (h3 r hr hz)
      omega
  exact ⟨hw (o1, s1) (by simp), hw (o2, s2) (by simp), by omega, fun hz => h3 (o2, s2) (by simp) hz⟩

/-! ## The named hypothesis -/

/-- **EIP-214, as a named hypothesis on the runner of messages**: a static message that succeeds
ends with no log. -/
def StaticNoLogs (_caller : Evm .fusaka Nat) (m : Message .fusaka) (child : Evm .fusaka Nat) : Prop :=
  m.isStatic = true → child.error = none → child.substate.logs.toList = []

/-- **Named hypothesis on the runner of messages**: a callee's output has fewer than `2 ^ 256` bytes,
so RETURNDATASIZE reports it exactly. (A callee pays for the memory it returns from out of gas below
`2 ^ 256`, so this holds of EthLib's runner; it is not yet derived here.) -/
def OutputFits (_caller : Evm .fusaka Nat) (_m : Message .fusaka) (child : Evm .fusaka Nat) : Prop :=
  child.output.size < 2 ^ 256

/-- What a STATICCALL cut asks of the callee frames of the runner. -/
def StaticOk (caller : Evm .fusaka Nat) (m : Message .fusaka) (child : Evm .fusaka Nat) : Prop :=
  StaticKept caller m child ∧ StaticNoLogs caller m child ∧ OutputFits caller m child

/-! ## Oracles of tables that extend each other -/

theorem tabResp_congr {oks oks' : List Bool} {outs outs' : List ByteArray} {n : Nat}
    (h1 : oks.getD n false = oks'.getD n false) (h2 : outs.getD n .empty = outs'.getD n .empty) :
    tabResp oks outs n = tabResp oks' outs' n := by
  funext k c v i
  simp only [tabResp, h1, h2]

/-- The oracles of two tables, one extending the other, agree at every world whose calls and GAS
reads the shorter answers. -/
theorem OS_le {codes : SolidCore.Solidity.Shared.Account.BytesMap} {T T' : RunTable} (hle : T.Le T')
    {w : List Event} (hn : (machineCalls w).length ≤ T.oks.length)
    (hn' : (machineCalls w).length ≤ T.outs.length) (h0 : 0 < T.oks.length) (h0' : 0 < T.outs.length)
    (hg : gasReads w ≤ T.gases.length) :
    (∀ name a, (OS codes T').env name w a = (OS codes T).env name w a) ∧
      (OS codes T').result w = (OS codes T).result w := by
  have hr : tabResp T'.oks T'.outs ((machineCalls w).length - 1) =
      tabResp T.oks T.outs ((machineCalls w).length - 1) :=
    tabResp_congr (getD_of_prefix hle.1 (by omega) _) (getD_of_prefix hle.2.1 (by omega) _)
  have hgas : gasReads w ≠ 0 →
      T'.gases.getD (gasReads w - 1) 0 = T.gases.getD (gasReads w - 1) 0 := fun h =>
    getD_of_prefix hle.2.2.2.2 (by omega) _
  refine ⟨fun name a => ?_, ?_⟩
  · simp only [OS, gasOracle]
    split_ifs with h
    · rw [hgas h.2.2]
    · simp only [envOracle, ethOracle, tabOracle_envEq, tabEnv, hr]
  · show tabResult T'.oks T'.outs w = tabResult T.oks T.outs w
    simp only [tabResult, hr]

/-! ## Segments under the oracles of tables that extend each other -/

/-- A frame's calls are among the messages it sent. -/
theorem machineCalls_length_le_sent : ∀ w : List Event, (machineCalls w).length ≤ sent w
  | [] => by simp [machineCalls, sent]
  | e :: w => by
    have ih := machineCalls_length_le_sent w
    unfold sent at ih ⊢
    cases e <;> simp [machineCalls, Event.sends, List.filter_cons] <;> omega

/-- **The oracles of a table and of any extension agree at the worlds the table answers**: every
world with at most `ng` GAS reads and `ns` messages, when the table holds `ng` gases and `ns`
flags and outputs. So a segment runs alike under both (`AssembleCut.execC_agree`), as
`AssembleCut.table_agree` gives for the failing world's oracle. -/
theorem OS_agreeT (codes : SolidCore.Solidity.Shared.Account.BytesMap) {T T' : RunTable}
    (hle : T.Le T') {ng ns : Nat} (hg : ng ≤ T.gases.length) (hn : ns ≤ T.oks.length)
    (hn' : ns ≤ T.outs.length) : Agree (OS codes T) (OS codes T') ng ns := by
  refine ⟨rfl, rfl, fun w hw hsw name a => ?_⟩
  have hgas : gasReads w ≠ 0 →
      T.gases.getD (gasReads w - 1) 0 = T'.gases.getD (gasReads w - 1) 0 := fun h =>
    (getD_of_prefix hle.2.2.2.2 (by omega) _).symm
  have hm := machineCalls_length_le_sent w
  simp only [OS, gasOracle]
  split_ifs with h
  · rw [hgas h.2.2]
  · simp only [envOracle, ethOracle, tabOracle_envEq]
    by_cases h0 : (machineCalls w).length = 0
    · have hnil : machineCalls w = [] := List.eq_nil_of_length_eq_zero h0
      simp [tabEnv, hnil]
    · have hr : tabResp T.oks T.outs ((machineCalls w).length - 1) =
          tabResp T'.oks T'.outs ((machineCalls w).length - 1) :=
        tabResp_congr (getD_of_prefix hle.1 (by omega) _).symm
          (getD_of_prefix hle.2.1 (by omega) _).symm
      simp only [tabEnv, hr]

/-- An effect that stops no segment adds no call to the frame's world. -/
theorem apply_calls {o : Oracle} {call : Call} {e : Effect} (he : cutEffect e = false)
    {args : List Word} {s s' : State} {r : Option Word}
    (h : Effect.apply o call e args s = some (r, s')) :
    machineCalls s'.world = machineCalls s.world := by
  unfold Effect.apply at h
  split at h <;> (try split at h) <;> simp_all [cutEffect]
  all_goals (obtain ⟨-, rfl⟩ := h; simp)

/-- **A segment adds no call to the frame's world**: the state it ends in, when it does not halt,
has the calls of the state it started from. With `AssembleCut.execC_agree`'s `Kept` (GAS reads and
messages), this keeps the table of a run's calls in step with the frame's calls between cuts. -/
theorem execC_calls (o : Oracle) (call : Call) (b : Nat) :
    ∀ (is : List Assemble.Instr) (S : List Word) (s s' : State),
      endState (execC o call b is S s) = some s' → machineCalls s'.world = machineCalls s.world
  | [], _, s, s', h => by simp [execC, endState] at h; subst h; rfl
  | .op op :: rest, S, s, s', h => by
    by_cases hc : cutOp op = true
    · simp only [execC, hc, ite_true, endState, Option.some.injEq] at h
      subst h; rfl
    · have hc' : cutOp op = false := by simpa using hc
      cases hs : SolarTV.EVM.Program.stepOp (SolarTV.EVM.Program.context o call s) op S s.memory with
      | error _ => simp [execC, hc', hs, endState] at h
      | ok r =>
        obtain ⟨S', m⟩ := r
        simp only [execC, hc', hs, Bool.false_eq_true, ite_false] at h
        exact execC_calls o call b rest S' { s with memory := m } s' h
  | .effect e a :: rest, S, s, s', h => by
    by_cases hc : cutEffect e = true
    · simp only [execC, hc, ite_true, endState, Option.some.injEq] at h
      subst h; rfl
    · have he : cutEffect e = false := by simpa using hc
      by_cases hl : S.length < a
      · simp [execC, he, hl, endState] at h
      · cases happ : Effect.apply o call e (S.take a) s with
        | none => simp [execC, he, hl, happ, endState] at h
        | some r =>
          obtain ⟨res, s1⟩ := r
          have hw := apply_calls he happ
          simp only [execC, he, hl, Bool.false_eq_true, ite_false, happ] at h
          split_ifs at h
          · simp [endState] at h
          · rw [execC_calls o call b rest _ s1 s' h, hw]
  | .jump t :: rest, S, s, s', h => by
    simp only [execC] at h
    split_ifs at h <;> simp [endState] at h
    subst h; rfl
  | .jumpi t :: rest, S, s, s', h => by
    simp only [execC] at h
    split_ifs at h
    · simp [endState] at h
    · cases S with
      | nil => simp [endState] at h
      | cons x S =>
        simp only at h
        split_ifs at h
        · exact execC_calls o call b rest S s s' h
        · simp [endState] at h; subst h; rfl
  | .pushLabel t :: rest, S, s, s', h => by
    simp only [execC] at h
    split_ifs at h
    · simp [endState] at h
    · exact execC_calls o call b rest _ s s' h
  | .jumpDyn :: rest, S, s, s', h => by
    cases S with
    | nil => simp [execC, endState] at h
    | cons x S => simp [execC, endState] at h; subst h; rfl
  | .jumpiDyn :: rest, S, s, s', h => by
    match S with
    | [] => simp [execC, endState] at h
    | [_] => simp [execC, endState] at h
    | x :: y :: S =>
      simp only [execC] at h
      split_ifs at h
      · exact execC_calls o call b rest S s s' h
      · simp [endState] at h; subst h; rfl
  | .jumpTable ts :: rest, S, s, s', h => by
    cases S with
    | nil => simp [execC, endState] at h
    | cons x S =>
      cases ht : ts[x.toNat]? with
      | none => simp [execC, ht, endState] at h
      | some t => simp [execC, ht, endState] at h; subst h; rfl
  | .stop :: rest, S, s, s', h => by simp [execC, endState] at h
  | .ret :: rest, S, s, s', h => by simp [execC, endState] at h; subst h; rfl
  | .revert :: rest, S, s, s', h => by simp [execC, endState] at h; subst h; rfl
  | .invalid :: rest, S, s, s', h => by simp [execC, endState] at h

/-! ## The cut -/

/-- The word of a masked address is the word modulo `2 ^ 160` (as EthLib's Base.Proofs.Address,
which the build of this library does not include). -/
theorem toNat_toU256_masked (w : U256) :
    (toAddressMasked w).toU256.toNat = w.toNat % 2 ^ 160 := by
  have h1 : (toAddressMasked w).toList = natToBytes 20 w.toNat := by
    rw [toAddressMasked, Vector.toList_drop, U256.toList_toBeBytes]
    rw [show 32 = 12 + 20 from rfl, natToBytes_add]
    exact List.drop_left' (natToBytes_length _ _)
  have h := bytesToNat_lt (toAddressMasked w).toList
  rw [Vector.length_toList] at h
  show (BitVec.ofNat 256 (bytesToNat (toAddressMasked w).toList)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h (by decide)), h1, bytesToNat_natToBytes]
  rfl

/-- What a STATICCALL to ECRECOVER (address 1) asks: the named EcrecoverAgree, a runner whose
frames for priced ECRECOVER messages are EthLib's (AssembleCallPre.meets_ecrecover), an account at
address 1 that is no EIP-7702 delegation, and at least ECRECOVER's price, 3000, passed on. -/
def PreOk (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop)
    (st : State.TransactionState) (ss : Substate) (M : ByteArray) (g : Nat)
    (asked addr inOff inSize outOff outSize : U256) : Prop :=
  addr.toNat % 2 ^ 160 = 1 ∧ AssembleCallPre.EcrecoverAgree ∧
    (∀ c m ch, P c m ch → AssembleCallPre.EcrecoverRuns c m ch) ∧
    (∀ cc, st.getCode (st.getAccount (toAddressMasked addr)).codeHash = .ok cc →
      delegatedAddress cc = none) ∧
    3000 ≤ (messageCallGas .fusaka 0 asked.toNat g
      (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).cost
      (if decide (toAddressMasked addr ∉ ss.accessedAddresses) then 2600 else 100)).subCall

open SolarTV.Machine in
/-- The input range of a STATICCALL, read from both memories once both ranges grew. -/
theorem read_eq2 {m : Mem} {M : ByteArray} {i isz o osz : Word} (hm : MemRel m M) :
    (memoryReadBytes (memoryExtend M (extendMemory M.size [(i, isz), (o, osz)]).expandBy) i.toNat
        isz.toNat).toList.map (·.toNat) =
      (((m.expand i.toNat isz.toNat).expand o.toNat osz.toNat).read i.toNat isz.toNat).map
        BitVec.toNat := by
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  by_cases hz : isz = 0
  · subst hz
    simp [memoryReadBytes, Mem.read]
  · have hfit : i.toNat + isz.toNat ≤
        (memoryExtend M (extendMemory M.size [(i, isz), (o, osz)]).expandBy).size := by
      have := le_ceil32_add_expandBy M.size [(i, isz), (o, osz)] (i, isz) (by simp) hz
      dsimp only at this
      rw [ceil32_of_mod hmod] at this
      rw [size_memoryExtend]
      have := le_ceil32 (i.toNat + isz.toNat)
      omega
    rw [toList_map_toNat, size_memoryReadBytes hfit]
    have hb : ((m.expand i.toNat isz.toNat).expand o.toNat osz.toNat).bytes = m.bytes := by
      unfold Mem.expand; split <;> split <;> rfl
    simp only [Mem.read, hb, List.map_map]
    apply List.map_congr_left
    intro k hk
    simp only [List.mem_range] at hk
    rw [byteAt_memoryReadBytes hfit, if_pos hk, byteAt_memoryExtend, Function.comp_apply,
      ← hm.2 (i.toNat + k), UInt8.toNat_toBitVec]

/-- A STATICCALL under the oracle of a run answers as the table's world does at that call
(`tabResp`): its flag, and its output as the return data until the next call. -/
theorem OS_ans (codes : SolidCore.Solidity.Shared.Account.BytesMap) (T : RunTable)
    (w : List SolarTV.Machine.Event) (gas addr : (BitVec 256)) (input : List SolarTV.Memory.Byte) (st tr : (BitVec 256) → (BitVec 256))
    (ok : Bool) (out : ByteArray)
    (hr : tabResp T.oks T.outs (machineCalls w).length .staticcall (addr.toNat % 2 ^ 160) 0
      (input.map BitVec.toNat) = (ok, out))
    (hsz : out.size < 2 ^ 256) :
    callFlag (OS codes T) (w ++ [.call .staticcall [gas, addr] input st tr]) =
        (if ok then 1 else 0) ∧
      ∀ rest, machineCalls rest = [] →
        RdRel (OS codes T) (w ++ [.call .staticcall [gas, addr] input st tr] ++ rest)
          out := by
  have hm := machineCalls_static w gas addr input st tr
  refine ⟨?_, fun rest hrest => ?_⟩
  · show (if tabResult T.oks T.outs _ = 0 then _ else _) = _
    simp only [tabResult, hm, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      List.length_append, List.length_singleton, Nat.add_sub_cancel, hr]
    cases ok <;> simp
  · have hmr : machineCalls (w ++ [.call .staticcall [gas, addr] input st tr] ++ rest) =
        machineCalls w ++ [(.staticcall, addr.toNat % 2 ^ 160, 0, input.map BitVec.toNat)] := by
      rw [machineCalls_append, hm, hrest, List.append_nil]
    refine ⟨?_, fun i hi => ?_⟩
    · show ((OS codes T).env "returndatasize" _ []).toNat = _
      rw [OS_env codes T _ _ _ (by decide) rfl]
      simp only [tabEnv, show ("returndatasize" = "extcodesize") = False by simp, ite_false, hmr,
        List.getLast?_append, List.getLast?_singleton, Option.some_or, List.length_append,
        List.length_singleton, Nat.add_sub_cancel, hr, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hsz
    · show ((OS codes T).env "returndata" _ [BitVec.ofNat 256 i]).setWidth 8 = _
      rw [OS_env codes T _ _ _ (by decide) rfl]
      simp only [tabEnv, show ("returndata" = "extcodesize") = False by simp, ite_false, hmr,
        List.getLast?_append, List.getLast?_singleton, Option.some_or, List.length_append,
        List.length_singleton, Nat.add_sub_cancel, hr]
      apply BitVec.eq_of_toNat_eq
      have hi' : i < 2 ^ 256 := by omega
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec,
        Nat.mod_eq_of_lt hi', EthLib.Base.byteAt, hi, dite_true]
      have := (out.get! i).toNat_lt
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [ByteArray.get!]
      clear this
      exact congrArg UInt8.toNat (data_getElem! _ i hi)

/-- **A STATICCALL to code, read back from a run that succeeds**, at the frame's own gas: the run's
table grows by the callee frame's flag and output, and under the oracle of every extension of it,
SolarTV's STATICCALL pushes that flag and leaves that return data, and the frame after it relates to
SolarTV's state as a block entry does (memory, storage, logs, the budget of memory and gas). -/
theorem staticcall_cut {code : ByteArray} {msg : Message .fusaka} {call : Call} {pc g G : Nat}
    {M : ByteArray} {st : State.TransactionState} {ss ss0 : Substate} {rd : ByteArray}
    {asked addr inOff inSize outOff outSize : U256} {Tr : List U256}
    {s : State} {evm : Evm .fusaka Nat}
    (codes : SolidCore.Solidity.Shared.Account.BytesMap) (T : RunTable)
    (hm : MemRel s.memory M) (R : Rel msg ss0 st ss s) (hb : MemBudget G M g) (hG : G < 2 ^ 300)
    (hat : At code msg pc (asked :: addr :: inOff :: inSize :: outOff :: outSize :: Tr) M g st ss
      rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop} (meets : Meets P runChild)
    (hPok : ∀ c m ch, P c m ch → StaticOk c m ch)
    (within : GasMeter.gasHeld evm.gas ≤ bound) {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none)
    (hto : toCode .staticcall (addr.toNat % 2 ^ 160) 0 = true ∨
      PreOk P st ss M g asked addr inOff inSize outOff outSize)
    (hoks : T.oks.length = (machineCalls s.world).length)
    (houts : T.outs.length = (machineCalls s.world).length)
    (hgr : gasReads s.world ≤ T.gases.length) :
    ∃ (ok : Bool) (out : ByteArray) (s' : State) (M' : ByteArray) (g' : Nat)
      (st' : State.TransactionState) (ss' : Substate) (m : Evm .fusaka Nat)
      (within' : GasMeter.gasHeld m.gas ≤ bound),
      (∀ T'', ({ T with oks := T.oks ++ [ok], outs := T.outs ++ [out] } : RunTable).Le T'' →
        Effect.apply (OS codes T'') call (.call .staticcall)
            [asked, addr, inOff, inSize, outOff, outSize] s =
          some (some (if ok then 1 else 0), s') ∧ RdRel (OS codes T'') s'.world out) ∧
      (∃ ev, s'.world = s.world ++ [ev] ∧ sent [ev] = 1 ∧ gasReads [ev] = 0 ∧
        (machineCalls [ev]).length = 1) ∧
      MemRel s'.memory M' ∧ Rel msg ss0 st' ss' s' ∧ MemBudget G M' g' ∧ g' ≤ g ∧
      At code msg (pc + 1) ((if ok then 1 else 0) :: Tr) M' g' st' ss' out m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨calleeCode, route, hcode, hroute, hg, caller, mm, child, after, within', g', hPP, -, hcs,
    hcsub, hms, hmv, hmc, hmt, htg, hmd, hmca, hmdp, hmgas, hg', hat', hrun'⟩ :=
    staticcall_back hat hlt hbyte hdepth meets within hrun hok
  have hP := hPok _ _ _ hPP
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  obtain ⟨hb1, hb2, hbud, hfit⟩ := budget_grow2 (pre := (if decide (toAddressMasked addr ∉
    ss.accessedAddresses) then 2600 else 100) +
      routeCost .fusaka (ss.accessedAddresses.insert (toAddressMasked addr)) route) hmod hb hG
    (by omega)
  -- The table with the call's flag and output.
  let T1 : RunTable := { T with oks := T.oks ++ [child.error.isNone], outs := T.outs ++ [child.output] }
  have hle1 : T.Le T1 := ⟨List.prefix_append _ _, List.prefix_append _ _, List.prefix_refl _,
    List.prefix_refl _, List.prefix_refl _⟩
  let ev : Event := .call .staticcall [asked, addr]
    (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
      inOff.toNat inSize.toNat) s.storage s.transient
  have hev : ∀ T'', T1.Le T'' →
      callFlag (OS codes T'') (s.world ++ [ev]) = (if child.error.isNone then 1 else 0) ∧
        RdRel (OS codes T'') (s.world ++ [ev]) child.output := by
    intro T'' hle
    have hok' : T''.oks.getD (machineCalls s.world).length false = child.error.isNone := by
      rw [getD_of_prefix hle.1 (by simp [T1, hoks])]
      simp [T1, hoks]
    have hout' : T''.outs.getD (machineCalls s.world).length .empty = child.output := by
      rw [getD_of_prefix hle.2.1 (by simp [T1, houts])]
      simp [T1, houts]
    have hresp : tabResp T''.oks T''.outs (machineCalls s.world).length .staticcall
        (addr.toNat % 2 ^ 160) 0
        ((((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
          inOff.toNat inSize.toNat).map BitVec.toNat) = (child.error.isNone, child.output) := by
      rcases hto with hto | ⟨h1, hag, hER, hnd, hg3⟩
      · simp only [tabResp, hto, ite_true]
        rw [hok', hout']
      · -- ECRECOVER: the source's answer, which the callee frame matches.
        have htc : toCode .staticcall (addr.toNat % 2 ^ 160) 0 = false := by rw [h1]; decide
        simp only [tabResp, htc, Bool.false_eq_true, ite_false]
        have hrn : route = none := by
          rcases route with _ | ⟨d, c'⟩
          · rfl
          · have := hroute.2.1
            rw [hnd _ hcode] at this
            cases this
        subst hrn
        have hmsg : AssembleCallPre.EcrecoverMsg mm := by
          refine ⟨by rw [htg]; rfl, ?_, by simpa using hmdp, hmv, ?_⟩
          · have h1' : (toAddressMasked addr).toU256.toNat = 1 := by
              rw [toNat_toU256_masked]; exact h1
            simp only [precompileAddress, hmca, routeAddr, h1']
            decide
          · rw [hmgas]
            simpa [routeCost] using hg3
        have hin : (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat
            outSize.toNat).read inOff.toNat inSize.toNat).map BitVec.toNat =
            SolidCore.Solidity.Source.byteArrayToBytes mm.data := by
          rw [hmd, ← read_eq2 hm]
          rfl
        rw [h1, hin]
        exact AssembleCallPre.ecrecover_answer hag (hER _ _ _ hPP) hmsg
    obtain ⟨hf, hr⟩ := OS_ans codes T'' s.world asked addr
      (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
        inOff.toNat inSize.toNat) s.storage s.transient _ _ hresp hP.2.2
    refine ⟨hf, ?_⟩
    have := hr [] rfl
    rw [List.append_nil] at this
    exact this
  -- SolarTV's STATICCALL under the table's oracle.
  obtain ⟨s', happ, hsto, htr, hrd, hw, hmem'⟩ := staticcall_effectW (o := OS codes T1) (call := call)
    (gas := asked) (addr := addr) (child := child) hm hb1 hb2 (hev T1 (RunTable.Le.refl _)).1
    (hev T1 (RunTable.Le.refl _)).2
  -- Under every extension it runs the same.
  have hsame : ∀ T'', T1.Le T'' →
      Effect.apply (OS codes T'') call (.call .staticcall)
          [asked, addr, inOff, inSize, outOff, outSize] s =
        Effect.apply (OS codes T1) call (.call .staticcall)
          [asked, addr, inOff, inSize, outOff, outSize] s := by
    intro T'' hle
    have hmc1 : (machineCalls (s.world ++ [ev])).length = (machineCalls s.world).length + 1 := by
      rw [machineCalls_static]
      simp
    obtain ⟨henv, hres⟩ := OS_le (codes := codes) hle (w := s.world ++ [ev])
      (by simp [T1, hmc1, hoks]) (by simp [T1, hmc1, houts]) (by simp [T1]) (by simp [T1])
      (by simp [T1, ev]; omega)
    have hflag : callFlag (OS codes T'') (s.world ++ [ev]) = callFlag (OS codes T1) (s.world ++ [ev]) := by
      simp only [callFlag, hres]
    have hbyte : returndataByte (OS codes T'') (s.world ++ [ev]) =
        returndataByte (OS codes T1) (s.world ++ [ev]) := by
      funext i
      simp only [returndataByte]
      rw [henv]
    simp only [ev] at henv hflag hbyte
    simp only [Effect.apply, CallKind.shape, called, returndataSize, hflag, henv, hbyte]
  refine ⟨child.error.isNone, child.output, s', _, g', (incorporateChild .fusaka caller child).state,
    (incorporateChild .fusaka caller child).substate, after, within', fun T'' hle => ?_,
    ⟨ev, hw, by simp [ev], by simp [ev], by simp [ev, machineCalls]⟩, hmem', ?_, ?_,
    by omega, ?_, hrun'⟩
  · rw [hsame T'' hle, happ]
    refine ⟨by cases child.error.isNone <;> rfl, ?_⟩
    rw [hw]
    exact (hev T'' hle).2
  · -- Storage and the account are the caller's; the logs are the frame's, with no log of the callee.
    have hso := staticcall_state hcode hroute hP.1 hcs hms hmv hmc hmt htg
    refine ⟨fun k => ?_, ?_, ?_⟩
    · rw [(hso msg.currentTarget (List.not_mem_nil)).2.1, hsto]
      exact R.storage k
    · rw [(hso msg.currentTarget (List.not_mem_nil)).1]
      exact R.account
    · obtain ⟨L, hL1, hL2⟩ := R.logs
      refine ⟨L, ?_, ?_⟩
      · have hlogs : (incorporateChild .fusaka caller child).substate.logs.toList = ss.logs.toList := by
          unfold incorporateChild
          split
          · rename_i hn
            have h0 := hP.2.1 hms (by simpa using hn)
            rcases route with _ | ⟨d, c'⟩ <;> simp [Array.toList_append, h0, hcsub, routeSub]
          · rcases route with _ | ⟨d, c'⟩ <;> simp [hcsub, routeSub]
        rw [hlogs, hL1]
      · rw [hw, List.filter_append]
        simpa [ev, isLogE] using hL2
  · unfold MemBudget
    rw [size_memoryWrite_of_fit, size_memoryExtend]
    · omega
    · intro h
      simp only [ByteArray.size_extract] at h ⊢
      have hz : outSize ≠ 0 := by
        intro hz
        simp [hz] at h
      have := hfit hz
      rw [size_memoryExtend]
      have := Nat.min_le_left outSize.toNat child.output.size
      omega
  · simpa using hat'

/-- info: 'SolidCore.Refinement.Solar.AssembleCallCut.staticcall_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms staticcall_cut

/-- info: 'SolidCore.Refinement.Solar.AssembleCallCut.OS_agreeT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OS_agreeT

/-- info: 'SolidCore.Refinement.Solar.AssembleCallCut.execC_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms execC_calls

end SolidCore.Refinement.Solar.AssembleCallCut
