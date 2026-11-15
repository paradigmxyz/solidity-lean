import Verify.Tactic
import SolidCore.Refinement.Corpus.C4

/-!
# c4: `add(uint8 x)` adds to a packed `uint8 v` and xors a packed `uint8 w`

The specification of `Main.add` in `scripts/refinement/corpus/c4.sol`
(`uint8 v; uint8 w = 7;` `v += x; w ^= x; return v;`), proved against SolidCore with the Loom
VC generator of `Verify.Basic`, on the scope of c4's refinement: every call of `add` on any
argument word below `2 ^ 256`, from the storage the constructor leaves. `v` and `w` share
slot 0, `v` in its low byte and `w` in the next, so the deployed storage is slot 0 = `7 * 256`.

From there `v + x` never overflows, so a clean `x < 2 ^ 8` returns `x` and leaves slot 0
holding `x + (7 ^ x) * 256`; the `Panic(0x11)` branch of the model is unreachable on the
scope. A dirty word reverts with empty data in SolidCore's ABI decoder and keeps the storage.

`model` is the function as a `SolM` program on any storage: it reads slot 0, panics when
`v + x` does not fit in `uint8`, and writes the packed `(v + x, w ^ x)` back, keeping the
slot's higher bytes. `run_add` ties it to SolidCore by symbolic evaluation of the interpreter
on a free word (`wide_symex`, clean and dirty alike), from the deployed state with the call's
storage written over it (`run_eq_at`), once `shape_of` gives that the checked contract's core
is the literal `coreLit` and its constructor leaves exactly slot 0 = `7 * 256` and no logs,
from c4's refinement (`Corpus.C4.shape_of`, the kernel's one conversion check of the type
checker's output, `kernel_rfl`). `sc_vcgen` proves the verification conditions.

`specAt` widens it to any storage that writes slot 0 (`scopeAt`): `run_add_at` runs SolidCore
on a symbolic slot-0 word, and `postAt` is the model's outcome from it (`model_ok`,
`model_panic`, `model_dirty`).
-/

namespace SolidCore.Verify.C4

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement.Corpus.C4

/-- SolidCore's core contract of c4's `Main`, as the type checker leaves it. -/
def coreLit : Contract :=
  { storageFields := [{ name := "v",
                        slot := 0,
                        ty? := some (SolidCore.Solidity.Source.Ty.uint256),
                        layout? := some (SolidCore.Solidity.Source.StorageLayout.scalar
                                     (SolidCore.Solidity.Source.Ty.uint256)),
                        transient := false,
                        packedOffset := 0,
                        packedBytes := 1,
                        packedSigned := false },
                      { name := "w",
                        slot := 0,
                        ty? := some (SolidCore.Solidity.Source.Ty.uint256),
                        layout? := some (SolidCore.Solidity.Source.StorageLayout.scalar
                                     (SolidCore.Solidity.Source.Ty.uint256)),
                        transient := false,
                        packedOffset := 1,
                        packedBytes := 1,
                        packedSigned := false }],
    immutableFields := [],
    eventDecls := [],
    errorDecls := [],
    functions := [{ name := "add",
                    selector? := some 33980010,
                    payable := false,
                    params := [{ name := "x", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 8],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "x")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   8
                                   (SolidCore.Solidity.Source.Expr.var "x")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.add))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 8))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "v"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "x")),
                                  SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.bitXor))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 8))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "w"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "x")),
                                  SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       8
                                       (SolidCore.Solidity.Source.Expr.storageRead
                                         (SolidCore.Solidity.Source.StorageReadMode.ref)
                                         "v"
                                         [])]]],
                    dispatchId? := none },
                  { name := "__internal_add(uint8)#[SolidCore.Solidity.Ty.uint 8]",
                    selector? := none,
                    payable := false,
                    params := [{ name := "x", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    paramAbiCleanups := [SolidCore.Solidity.Source.AbiCleanup.uint 8],
                    returns := [{ name := "_ret0", ty := SolidCore.Solidity.Source.Ty.uint256, isStorageRef := false }],
                    body := SolidCore.Solidity.Source.Stmt.block
                              [SolidCore.Solidity.Source.Stmt.assign
                                 (SolidCore.Solidity.Source.LValue.var "x")
                                 (SolidCore.Solidity.Source.Expr.castOp
                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                   8
                                   (SolidCore.Solidity.Source.Expr.var "x")),
                               SolidCore.Solidity.Source.Stmt.skip,
                               SolidCore.Solidity.Source.Stmt.block
                                 [SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.add))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 8))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "v"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "x")),
                                  SolidCore.Solidity.Source.Stmt.exprStmt
                                    (SolidCore.Solidity.Source.Expr.assignment
                                      (some (SolidCore.Solidity.Source.BinaryOp.bitXor))
                                      (some (SolidCore.Solidity.Source.ValueCleanup.uint 8))
                                      (SolidCore.Solidity.Source.Expr.storageRead
                                        (SolidCore.Solidity.Source.StorageReadMode.header)
                                        "w"
                                        [])
                                      (SolidCore.Solidity.Source.Expr.var "x")),
                                  SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       8
                                       (SolidCore.Solidity.Source.Expr.storageRead
                                         (SolidCore.Solidity.Source.StorageReadMode.ref)
                                         "v"
                                         [])]]],
                    dispatchId? := none }] }

/-- `coreLit` is the refinement's print of the core, `Corpus.C4.coreLit`. -/
theorem coreLit_eq : coreLit = Corpus.C4.coreLit := rfl

/-- The storage the constructor leaves: `v = 0` in the low byte of slot 0, `w = 7` in the
next. -/
def deployed : List (Nat × Nat) := [(0, 7 * 256)]

/-- `add` as a Loom program over the storage: a dirty word reverts with empty data; else
`v` (the low byte of slot 0) plus `x` panics when it overflows `uint8`, and otherwise slot 0
gets `v + x` in its low byte and `w ^ x` in the next, and the call returns `v + x`. -/
def model (ws : List Nat) : SolM (List Nat) :=
  if ws.getD 0 0 < 2 ^ 8 then do
    let s0 ← sload 0
    if s0 % 2 ^ 8 + ws.getD 0 0 < 2 ^ 8 then do
      sstore 0 (s0 / 2 ^ 16 * 2 ^ 16 + (s0 / 2 ^ 8 % 2 ^ 8 ^^^ ws.getD 0 0) * 2 ^ 8 +
        (s0 % 2 ^ 8 + ws.getD 0 0))
      pure (word (s0 % 2 ^ 8 + ws.getD 0 0))
    else revert (panic 0x11)
  else revert []

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore runs `add` on any argument word, from the deployed storage, as `model` does. -/
theorem run_add {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d deployed) (w : U256) :
    Source.run fuel c (callAt Bytecode.C4.Main.addSelector [w] deployed) =
      some (observe (slotValue deployed) (model [w.toNat] (slotValue deployed))) := by
  rw [run_eq_at hd]
  have hev := hd.events
  have hnone : ∀ k, k ≠ 0 → d.storage.get? k = none := fun k hk => by
    rw [Std.HashMap.get?_eq_getElem?]
    exact hd.getElem?_eq_none (by simp [deployed]; omega)
  simp only [hcore, List.map_cons, List.map_nil, deployed, List.foldl_cons, List.foldl_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, Bytecode.C4.Main.addSelector,
    get?_insert]
  all_goals
    have hw := w.isLt
    generalize BitVec.toNat w = x at *
    simp only [Nat.reducePow] at hw
  · have h1 : (1792 + x) % 2 ^ 256 = 1792 + x := Nat.mod_eq_of_lt (by omega)
    simp only [Nat.reducePow] at h1
    have h2 : (1792 + x) / 256 % 256 = 7 := by omega
    have h3 : 1792 + x - 7 * 256 = x := by omega
    have h4 : (7 ^^^ x) < 256 := Nat.xor_lt_two_pow (n := 8) (by omega) (by omega)
    simp only [h1, h2, h3]
    simp [Source.observe, observe, model, sload, sstore, bind, StateT.bind, pure, StateT.pure,
      Except.bind, Except.pure, slotValue, callAt, State.loadSlot, StorageMap.lookup?, get?_insert,
      hev, State.logEntries, *, Nat.mod_eq_of_lt, word]
    funext slot
    simp only [Std.HashMap.getElem?_insert, Shared.norm, Shared.wordModulus, beq_iff_eq]
    try rw [show EvmYul.UInt256.size = 2 ^ 256 from rfl]
    generalize slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = k
    by_cases h : k = 0
    · subst h; simp; rw [Nat.add_comm]
    · have h' : ¬0 = k := fun e => h e.symm
      have := hnone k h
      rw [Std.HashMap.get?_eq_getElem?] at this
      simp [h, h', this]
  · simp [Source.observe, observe, model, revert, slotValue, callAt, State.loadSlot,
      StorageMap.lookup?, get?_insert, hev, State.logEntries, *]
    funext k
    simp only [slotValue, List.foldl_cons, List.foldl_nil]

/-- The calls of the specification: `add` on any argument word, clean or dirty, from the
deployed storage, the scope of c4's refinement (`Corpus.C4.refines_full`). -/
def scope : Call → Prop := fullScope fns deployed

/-- No precondition beyond the scope. -/
def pre : Call → Prop := fun _ => True

/-- `add(x)` from the deployed storage (`v = 0`, `w = 7`): on a clean `x < 2 ^ 8` it returns
`v + x = x` and leaves slot 0 holding `v' = x` in its low byte and `w' = 7 ^ x` in the next,
every other slot 0; on a dirty word it reverts with empty data and keeps the storage. It
emits no logs. -/
def post (call : Call) (obs : Observable) : Prop :=
  let x := (argWords 1 call).getD 0 0
  (if x < 2 ^ 8 then
    obs.success = true ∧ obs.output = word x ∧
      ∀ slot, obs.storage slot = if slot % 2 ^ 256 = 0 then x + (7 ^^^ x) * 2 ^ 8 else 0
   else
    obs.success = false ∧ obs.output = [] ∧ ∀ slot, obs.storage slot = slotValue deployed slot) ∧
  obs.logs = []

/-- The checked contract has the core `coreLit`, and its constructor leaves exactly
`deployed` and no logs: `Corpus.C4.shape_of`, the kernel's conversion check of the type
checker's output (`kernel_rfl`). -/
theorem shape_of {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    c.core = coreLit ∧ deployedStorage fuel c = some deployed ∧
      deployedAt fuel c deployed = true := by
  obtain ⟨hk, hs, he⟩ := Corpus.C4.shape_of hc
  exact ⟨hk.trans coreLit_eq.symm, hs, he⟩

/-- `model` implements SolidCore's `Main` on every call of the scope. -/
theorem implements {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d deployed) : Implements fuel c scope (argWords 1) model :=
  implements_of_run' (by simp [fns]) fun fn hfn ws hl => by
    simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
    subst hfn
    rcases ws with _ | ⟨w, _ | _⟩ <;> simp at hl
    exact run_add hcore hd w

/-- The verification conditions of `add`, by Loom's weakest preconditions. -/
theorem vcs : ∀ call, scope call → pre call → vc model (argWords 1) post call := by
  sc_vcgen [scope, fns, model, post, deployed]

/-- **The specification of `c4`'s `add`**, as a triple against SolidCore. -/
theorem spec : ∃ c, contract? = .ok c ∧ deployedStorage fuel c = some deployed ∧
    Triple fuel c scope pre post := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hk, hs, hdep⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployedAt_of hdep
  exact ⟨c, hc, hs, triple_of_wp (implements hk hd) vcs⟩

/-- The specification of `c4`'s `add` as `Satisfies` on SolidCore. -/
theorem satisfies : ∃ c, contract? = .ok c ∧ deployedStorage fuel c = some deployed ∧
    Satisfies (solidCore fuel) c scope pre post := by
  obtain ⟨c, hc, hs, h⟩ := spec
  exact ⟨c, hc, hs, satisfies_of_triple h⟩

/-! ## From any storage

specAt states the specification on scopeAt, every call of add with no value from any storage σ
that gives slot 0 a word (an entry whose key is 0 modulo 2 ^ 256), the slot v and w share.
SolidCore runs a call from σ written over the deployed storage (run_eq_at), so a storage without
an entry for slot 0 would read the constructor's word 7 * 256 there, which the call's storage
does not show; every other slot reads as σ's, since the constructor writes slot 0 alone.
postAt is the model's outcome from σ: with s0 = slotValue σ 0, a clean x < 2 ^ 8 returns
v + x = s0 % 2 ^ 8 + x and leaves slot 0 with its high bytes kept, w ^ x in its second byte and
v + x in its low byte when v + x fits in uint8, and otherwise reverts with Panic(0x11); a dirty
word reverts with empty data. A revert keeps σ, and no call logs. -/

/-- The last write of a slot among σ, over any earlier word, is slotValue's when σ writes the
slot. -/
theorem foldl_some_of_mem (σ : List (Nat × Nat)) (q : Nat) (hq : q < 2 ^ 256) (a : Option Nat)
    (b : Nat) (h : a = some b ∨ ∃ kv ∈ σ, kv.1 % 2 ^ 256 = q) :
    σ.foldl (fun acc kv => if Shared.norm kv.1 = q then some (Shared.norm kv.2) else acc) a =
      some (σ.foldl (fun acc kv => if kv.1 % 2 ^ 256 = q % 2 ^ 256 then kv.2 % 2 ^ 256 else acc) b) := by
  induction σ generalizing a b with
  | nil =>
    rcases h with h | ⟨_, h, _⟩
    · simpa using h
    · simp at h
  | cons kv σ ih =>
    simp only [List.foldl_cons]
    apply ih
    by_cases hk : kv.1 % 2 ^ 256 = q
    · left
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show Shared.norm kv.1 = q from hk)),
        ite_eq_left_of_eq_true _ _ (eq_true (show kv.1 % 2 ^ 256 = q % 2 ^ 256 by
          rw [Nat.mod_eq_of_lt hq]; exact hk))]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ Shared.norm kv.1 = q from hk)),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ kv.1 % 2 ^ 256 = q % 2 ^ 256 by
          rw [Nat.mod_eq_of_lt hq]; exact hk))]
      rcases h with h | ⟨kv', h', hq'⟩
      · exact Or.inl h
      · rcases List.mem_cons.1 h' with rfl | h'
        · exact absurd hq' hk
        · exact Or.inr ⟨kv', h', hq'⟩

theorem model_dirty (x : Nat) (s : Storage) (hx : ¬ x < 256) : model [x] s = .error [] := by
  simp [model, hx, revert]

theorem model_panic (x : Nat) (s : Storage) (hx : x < 256) (h : ¬ s 0 % 256 + x < 256) :
    model [x] s = .error (panic 0x11) := by
  simp [model, hx, h, revert, sload, bind, StateT.bind, Except.bind]

theorem model_ok (x : Nat) (s : Storage) (hx : x < 256) (h : s 0 % 256 + x < 256) :
    model [x] s = .ok (word (s 0 % 256 + x), fun k => if k % 2 ^ 256 = 0 then
      (s 0 / 65536 * 65536 + (s 0 / 256 % 256 ^^^ x) * 256 + (s 0 % 256 + x)) % 2 ^ 256
      else s k) := by
  simp [model, hx, h, sload, sstore, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure]

/-- The calls of add on any argument word, with no value, from any storage that writes slot 0. -/
def scopeAt : Call → Prop := fun call => ∃ σ, (∃ kv ∈ σ, kv.1 % 2 ^ 256 = 0) ∧ fullScope fns σ call

/-- The deployed scope is the scope from any storage at the deployed storage, which writes
slot 0. -/
theorem scopeAt_of_scope {call : Call} (h : scope call) : scopeAt call :=
  ⟨deployed, ⟨(0, 7 * 256), List.mem_singleton_self _, rfl⟩, h⟩

/-- add(x) from the storage of the call, with s0 its slot 0: v + x = s0 % 2 ^ 8 + x returned and
slot 0 holding s0's high bytes, w ^ x and v + x when x is clean and v + x fits in uint8, a
Panic(0x11) revert when it does not, and a revert with empty data on a dirty word. A revert
keeps the storage, and no call logs. -/
def postAt (call : Call) (obs : Observable) : Prop :=
  let x := (argWords 1 call).getD 0 0
  let s0 := slotValue call.storage 0
  (if x < 2 ^ 8 then
    if s0 % 2 ^ 8 + x < 2 ^ 8 then
      obs.success = true ∧ obs.output = word (s0 % 2 ^ 8 + x) ∧
        ∀ slot, obs.storage slot = if slot % 2 ^ 256 = 0 then
          s0 / 2 ^ 16 * 2 ^ 16 + (s0 / 2 ^ 8 % 2 ^ 8 ^^^ x) * 2 ^ 8 + (s0 % 2 ^ 8 + x)
        else slotValue call.storage slot
    else
      obs.success = false ∧ obs.output = panic 0x11 ∧
        ∀ slot, obs.storage slot = slotValue call.storage slot
   else
    obs.success = false ∧ obs.output = [] ∧ ∀ slot, obs.storage slot = slotValue call.storage slot) ∧
  obs.logs = []

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore runs add on any argument word, from any storage σ that writes slot 0, as model
does. -/
theorem run_add_at {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d deployed) (w : U256) (σ : List (Nat × Nat))
    (hσ : ∃ kv ∈ σ, kv.1 % 2 ^ 256 = 0) :
    Source.run fuel c (callAt Bytecode.C4.Main.addSelector [w] σ) =
      some (observe (slotValue σ) (model [w.toNat] (slotValue σ))) := by
  rw [run_eq_at hd]
  have hev := hd.events
  have hm0 : (σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage)[0]? =
      some (slotValue σ 0) := by
    rw [getElem?_foldl_insertLoop]
    exact foldl_some_of_mem σ 0 (by decide) _ 0 (Or.inr hσ)
  have hmk : ∀ k, k % 2 ^ 256 ≠ 0 →
      ((σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage)[k % 2 ^ 256]?).getD 0 =
        slotValue σ k := by
    intro k hk
    rw [getElem?_foldl_insertLoop, hd.getElem?_eq_none (by simp [deployed]; omega)]
    exact getD_foldl σ k none 0 rfl
  generalize σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage = m at hm0 hmk
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, Bytecode.C4.Main.addSelector, hm0]
  all_goals
    have hw := w.isLt
    have hs := slotValue_lt σ 0
    generalize BitVec.toNat w = x at *
    simp only [Nat.reducePow] at hw hs
  · -- Panic(0x11): v + x overflows uint8.
    rw [model_panic x _ (by omega) (by omega)]
    simp [Source.observe, observe, callAt, panic, word]
  · -- v + x fits.
    rw [model_ok x _ (by omega) (by omega)]
    generalize slotValue σ 0 = s0 at *
    have hA : (s0 % 2 ^ 256 - s0 % 256 + (s0 + x) % 256) % 2 ^ 256 = s0 + x := by omega
    have hW : (s0 + x) / 256 % 256 = s0 / 256 % 256 := by omega
    have hO : (s0 + x - s0 / 256 % 256 * 256) % 256 = s0 % 256 + x := by omega
    simp only [Nat.reducePow] at hA
    simp only [hA, hW, hO]
    have hy : (s0 / 256 % 256 ^^^ x) < 256 := Nat.xor_lt_two_pow (n := 8) (by omega) (by omega)
    generalize (s0 / 256 % 256 ^^^ x) = y at *
    have hB : s0 + x - s0 / 256 % 256 * 256 + y * 256 =
        s0 / 65536 * 65536 + y * 256 + (s0 % 256 + x) := by omega
    simp only [hB]
    simp [Source.observe, observe, State.loadSlot, StorageMap.lookup?, State.logEntries, word]
    funext slot
    have hk := hmk slot
    simp only [Std.HashMap.getElem?_insert, Shared.norm, Shared.wordModulus, beq_iff_eq,
      EvmYul.UInt256.size, Nat.reducePow] at hk ⊢
    generalize slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = k at hk ⊢
    by_cases h : k = 0
    · subst h
      simp
    · have h' : ¬0 = k := fun e => h e.symm
      rw [← hk h]
      simp only [h, h', ↓reduceIte]
      cases m[k]? <;> rfl
  · -- A dirty word reverts with no data.
    rw [model_dirty x _ (by omega)]
    simp [Source.observe, observe, callAt]

/-- model implements SolidCore's Main on every call of scopeAt. -/
theorem implementsAt {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d deployed) : Implements fuel c scopeAt (argWords 1) model := by
  rintro call ⟨σ, hσ, hs⟩
  refine implements_of_run' (s := σ) (by simp [fns]) (fun fn hfn ws hl => ?_) call hs
  simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  subst hfn
  rcases ws with _ | ⟨w, _ | _⟩ <;> simp at hl
  exact run_add_at hcore hd w σ hσ

/-- The verification conditions of add from any storage, from model's outcomes. -/
theorem vcsAt : ∀ call, scopeAt call → pre call → vc model (argWords 1) postAt call := by
  rintro call ⟨σ, -, hs⟩ hp
  refine vcs_of_fullScope (fns := fns) (s := σ) (n := 1) (by simp [fns]) ?_ call hs hp
  intro fn hfn call args hcall hw hlen hargs hinit _
  subst hcall
  match args, hlen with
  | [x], _ =>
    have hx : x < 2 ^ 256 := hargs x (by simp)
    have hs0 := slotValue_lt σ 0
    rw [wp_eq]
    simp only [postAt, hw, List.getD_cons_zero]
    by_cases h1 : x < 256
    · by_cases h2 : slotValue σ 0 % 256 + x < 256
      · rw [model_ok x _ h1 h2]
        simp only [Nat.reducePow, h1, h2, ↓reduceIte, true_and]
        refine ⟨fun slot => ?_, trivial⟩
        split
        · exact Nat.mod_eq_of_lt (by
            have := Nat.xor_lt_two_pow (n := 8) (x := slotValue σ 0 / 256 % 256) (y := x)
              (by omega) (by omega)
            omega)
        · rfl
      · rw [model_panic x _ h1 h2]
        simp [h1, h2]
    · rw [model_dirty x _ h1]
      simp [h1]

/-- **The specification of c4's add from any storage**, as a triple against SolidCore. -/
theorem specAt : ∃ c, contract? = .ok c ∧ Triple fuel c scopeAt pre postAt := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hk, _, hdep⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployedAt_of hdep
  exact ⟨c, hc, triple_of_wp (implementsAt hk hd) vcsAt⟩

/-- The specification from any storage as Satisfies on SolidCore. -/
theorem satisfiesAt : ∃ c, contract? = .ok c ∧ Satisfies (solidCore fuel) c scopeAt pre postAt := by
  obtain ⟨c, hc, h⟩ := specAt
  exact ⟨c, hc, satisfies_of_triple h⟩

end SolidCore.Verify.C4
