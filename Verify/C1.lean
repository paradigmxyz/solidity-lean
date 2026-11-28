import Verify.Tactic
import SolidCore.Refinement.Corpus.C1

/-!
# c1: `f(uint8 x)` returns `x * 3 + 1`, or panics on overflow

The specification of `Main.f` in `scripts/refinement/corpus/c1.sol`, proved against SolidCore
with the Loom VC generator of `Verify.Basic`: on every call of `f` with a clean argument
word `x < 256`, from the deployed (empty) storage, the call returns the word `3 * x + 1` when
`x ≤ 84`, and reverts with `Panic(0x11)` when `x ≥ 85`, the first argument for which
`x * 3 + 1` does not fit in `uint8`; it emits no logs and leaves storage empty.

`model` is the function as a `SolM` program. `run_f` ties it to SolidCore by symbolic
evaluation of the interpreter on a free clean word (`wide_symex`), once `shape_of` gives
that the checked contract's core is the literal `coreLit` and its constructor leaves empty
storage and no logs, from c1's refinement (`Corpus.C1.shape_of`, the kernel's one conversion
check of the type checker's output, `kernel_rfl`); `implements_of_run` turns it into
`Implements`. `sc_vcgen` proves the verification conditions on every argument word, which
`vcs_mono` restricts to the scope.
-/

namespace SolidCore.Verify.C1

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement.Corpus.C1

/-- `f` as a Loom program over the storage. -/
def model (ws : List Nat) : SolM (List Nat) :=
  if ws.getD 0 0 * 3 + 1 < 2 ^ 8 then pure (word (ws.getD 0 0 * 3 + 1)) else revert (panic 0x11)

/-- The calls of the specification: `f` on every clean argument word, from the deployed
storage, the scope of c1's refinement (`Corpus.C1.scope []`). -/
def scope : Call → Prop := (· ∈ calls fns [[]])

/-- The precondition: none beyond the scope. -/
def pre : Call → Prop := fun _ => True

/-- `f(x)` returns `3 * x + 1` for `x ≤ 84` and reverts with `Panic(0x11)` for `x ≥ 85`,
with no logs and empty storage. -/
def post (call : Call) (obs : Observable) : Prop :=
  let x := (argWords 1 call).getD 0 0
  (x ≤ 84 → obs.success = true ∧ obs.output = word (3 * x + 1)) ∧
  (85 ≤ x → obs.success = false ∧ obs.output = panic 0x11) ∧
  obs.logs = [] ∧ ∀ slot, obs.storage slot = 0

/-- SolidCore's core contract of c1's `Main`, as the type checker leaves it. -/
def coreLit : Contract :=
  { storageFields := [],
    immutableFields := [],
    eventDecls := [],
    errorDecls := [],
    functions := [{ name := "f",
                    selector? := some 824235060,
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
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       8
                                       (SolidCore.Solidity.Source.Expr.castOp
                                         (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                         8
                                         (SolidCore.Solidity.Source.Expr.binary
                                           (SolidCore.Solidity.Source.BinaryOp.add)
                                           (SolidCore.Solidity.Source.Expr.castOp
                                             (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                             8
                                             (SolidCore.Solidity.Source.Expr.castOp
                                               (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                               8
                                               (SolidCore.Solidity.Source.Expr.binary
                                                 (SolidCore.Solidity.Source.BinaryOp.mul)
                                                 (SolidCore.Solidity.Source.Expr.castOp
                                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                                   8
                                                   (SolidCore.Solidity.Source.Expr.var "x"))
                                                 (SolidCore.Solidity.Source.Expr.castOp
                                                   (SolidCore.Solidity.Source.CastKind.uintCast)
                                                   8
                                                   (SolidCore.Solidity.Source.Expr.word 3)))))
                                           (SolidCore.Solidity.Source.Expr.castOp
                                             (SolidCore.Solidity.Source.CastKind.uintCast)
                                             8
                                             (SolidCore.Solidity.Source.Expr.word 1))))]]],
                    dispatchId? := none },
                  { name := "__internal_f(uint8)#[SolidCore.Solidity.Ty.uint 8]",
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
                                 [SolidCore.Solidity.Source.Stmt.returnValues
                                    [SolidCore.Solidity.Source.Expr.castOp
                                       (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                       8
                                       (SolidCore.Solidity.Source.Expr.castOp
                                         (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                         8
                                         (SolidCore.Solidity.Source.Expr.binary
                                           (SolidCore.Solidity.Source.BinaryOp.add)
                                           (SolidCore.Solidity.Source.Expr.castOp
                                             (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                             8
                                             (SolidCore.Solidity.Source.Expr.castOp
                                               (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                               8
                                               (SolidCore.Solidity.Source.Expr.binary
                                                 (SolidCore.Solidity.Source.BinaryOp.mul)
                                                 (SolidCore.Solidity.Source.Expr.castOp
                                                   (SolidCore.Solidity.Source.CastKind.uintCleanup)
                                                   8
                                                   (SolidCore.Solidity.Source.Expr.var "x"))
                                                 (SolidCore.Solidity.Source.Expr.castOp
                                                   (SolidCore.Solidity.Source.CastKind.uintCast)
                                                   8
                                                   (SolidCore.Solidity.Source.Expr.word 3)))))
                                           (SolidCore.Solidity.Source.Expr.castOp
                                             (SolidCore.Solidity.Source.CastKind.uintCast)
                                             8
                                             (SolidCore.Solidity.Source.Expr.word 1))))]]],
                    dispatchId? := none }] }

/-- `coreLit` is the refinement's print of the core, `Corpus.C1.coreLit`. -/
theorem coreLit_eq : coreLit = Corpus.C1.coreLit := rfl

/-- The checked contract has the core `coreLit`, and its constructor leaves empty storage and
no logs: `Corpus.C1.shape_of`, the kernel's conversion check of the type checker's output
(`kernel_rfl`). -/
theorem shape_of {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    c.core = coreLit ∧ deployedStorage fuel c = some [] ∧ ∃ d, DeployedAt fuel c d [] := by
  obtain ⟨hk, hs, he⟩ := Corpus.C1.shape_of hc
  obtain ⟨d, hd⟩ := deployed_of he
  exact ⟨hk.trans coreLit_eq.symm, hs, d, deployedAt_of_deployed hd⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore runs `f` on any clean argument word as `model` does. -/
theorem run_f {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d []) (w : U256) (hw : w.toNat < 2 ^ 8) :
    Source.run fuel c (callAt Bytecode.C1.Main.fSelector [w] []) =
      some (observe (slotValue []) (model [w.toNat] (slotValue []))) := by
  rw [run_eq_at hd]
  have hev := hd.events
  have hs : d.storage.isEmpty = true := by
    rw [← Std.HashMap.isEmpty_toList, hd.storage]; rfl
  simp only [Nat.reducePow] at hw
  simp only [hcore, List.map_cons, List.map_nil, List.foldl_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, Bytecode.C1.Main.fSelector]
  all_goals
    simp only [model, List.getD_cons_zero]
    split
  all_goals
    try rw [Nat.mod_eq_of_lt (by omega)]
    simp [Source.observe, observe, revert, pure, StateT.pure, Except.pure, panic, word,
      State.logEntries, State.loadSlot, StorageMap.lookup?, getElem?_of_isEmpty hs, hev,
      slotValue, callAt]
  all_goals first
    | (funext k; rfl)
    | (simp (disch := omega) only [Nat.reducePow, Nat.mod_eq_of_lt] at *; omega)

/-- Every call of the scope is a call of `Abi.fullScope` on a clean word. -/
theorem scope_sub (call : Call) (h : scope call) :
    fullScope fns [] call ∧ (argWords 1 call).getD 0 0 < 2 ^ 8 := by
  simp only [scope, calls, fns, tuples, Param.values, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_left] at h
  obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := h
  have hb : ∀ b ∈ [a], b < 2 ^ 256 := by simp; omega
  refine ⟨⟨_, List.mem_singleton_self _, [a], rfl, hb, rfl⟩, ?_⟩
  rw [show argWords 1 _ = [a] from argWords_calldata _ [a] hb 0 []]
  simpa using ha

/-- `model` implements SolidCore's `Main` on every call of the scope. -/
theorem implements {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d []) : Implements fuel c scope (argWords 1) model :=
  (implements_of_run (ok := fun ws => ws.getD 0 0 < 2 ^ 8) (by simp [fns])
    fun fn hfn ws hl hok => by
      simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
      subst hfn
      rcases ws with _ | ⟨w, _ | _⟩ <;> simp at hl
      exact run_f hcore hd w (by simpa using hok)).mono scope_sub

/-- The verification conditions of `f`, by Loom's weakest preconditions. -/
theorem vcs : ∀ call, scope call → pre call → vc model (argWords 1) post call :=
  vcs_mono (scope := fullScope fns []) (by sc_vcgen [fns, model, post])
    fun call h => (scope_sub call h).1

/-- **The specification of `c1`'s `f`**, as a triple against SolidCore. -/
theorem spec : ∃ c, contract? = .ok c ∧ deployedStorage fuel c = some [] ∧
    Triple fuel c scope pre post := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hk, hs, d, hd⟩ := shape_of hc
  exact ⟨c, hc, hs, triple_of_wp (implements hk hd) vcs⟩

/-- The specification of `c1`'s `f` as `Satisfies` on SolidCore. -/
theorem satisfies : ∃ c, contract? = .ok c ∧ deployedStorage fuel c = some [] ∧
    Satisfies (solidCore fuel) c scope pre post := by
  obtain ⟨c, hc, hs, h⟩ := spec
  exact ⟨c, hc, hs, satisfies_of_triple h⟩

end SolidCore.Verify.C1
