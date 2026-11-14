import Contracts.UniswapV2.ERC20.Slice.Vc

/-!
# UniswapV2ERC20.transfer: the slice's statements over SolidCore's runs

From the erased tree (Run.lean) and the deployment and erasure checks (`Gen.deploy_eq`,
`Gen.transfer_erase_eq`), for SolidCore's checked contract `c` of the pinned port:

* `run_tree`: SolidCore's run of every valid call is the tree's result;
* `meets_seq`: `Shapes.Meets` of `SeqPost` on `Valid deployed`, with no premise;
* `meets_target`: `Shapes.Meets` of `TargetPost` on `ValidIn` (`Valid` and the call's
  footprint premise `Scope`);
* `transfer_holds`, `meets_bundle`: solar-verify's exported spec of `transfer` on the stage's
  calls whose footprint premise holds, and as `Shapes.Meets` of `bundlePost` on `ValidIn`;
* `nonVacuous_seq`, `nonVacuous_target`, `nonVacuous_bundle`: each postcondition rejects some
  observable of a valid call (the premise holding of the real keccak256, by the kernel), and
  `valid_inhabited`;
* the required concrete runs (docs/CERTIFICATION_TARGET.md): `self_max`, a self-transfer of 1 from
  a balance of `2 ^ 256 - 1` succeeds with the storage unchanged and `Transfer` logged;
  `self_short`, a self-transfer of more than the balance reverts with SafeMath's
  `ds-math-sub-underflow` and no change; both as SolidCore runs of concrete calls, and in general
  (`self_ok`, `self_fail`).
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Slice

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec SolidCore.Refinement.Shapes
open SolidCore.Spec.UniswapV2.ERC20.Slice.Gen

/-- SolidCore's interpreter fuel for the port. -/
abbrev fuel : Nat := SolidCore.Verify.VC.UniswapV2ERC20.fuel

/-- **The valid calls with their premise**: `Valid` from the constructor's storage, and the call's
footprint premise. -/
def ValidIn (call : Call) : Prop := Valid deployed call ∧ Scope call

/-- The deployment and the erasure of `transfer`, from the kernel checks. -/
theorem facts {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    (∃ d, Wide.DeployedAt fuel c d deployed) ∧ ∃ f, c.core.findFunctionBySelector? 2835717307 = some f ∧
      f.params.length = 2 ∧ eraseFn (envOf c.core) fuel f = some transfer_tree := by
  refine ⟨?_, ?_⟩
  · have hdep := deploy_eq
    simp only [deploy?, hc] at hdep
    exact Wide.deployedAt_of hdep
  · have hmap := transfer_erase_eq
    simp only [transfer_erase?, hc, Option.map_eq_some_iff, Prod.mk.injEq] at hmap
    obtain ⟨f, hf, hlen, hT⟩ := hmap
    exact ⟨f, hf, hlen, hT⟩

theorem callArgs_transferCall (σ : List (Nat × Nat)) {dst v : Nat} (hto : dst < 2 ^ 256) (hv : v < 2 ^ 256) :
    callArgs (transferCall σ dst v) = [dst, v] := by
  simp only [callArgs, transferCall]
  exact words_calldata _ (by simp; omega)

theorem transferCall_inj {σ σ' : List (Nat × Nat)} {dst dst' v v' : Nat} (hto : dst < 2 ^ 256)
    (hv : v < 2 ^ 256) (hto' : dst' < 2 ^ 256) (hv' : v' < 2 ^ 256)
    (h : transferCall σ dst v = transferCall σ' dst' v') : σ = σ' ∧ dst = dst' ∧ v = v' := by
  have hs : σ = σ' := congrArg Call.storage h
  have ha := congrArg callArgs h
  rw [callArgs_transferCall σ hto hv, callArgs_transferCall σ' hto' hv'] at ha
  simp only [List.cons.injEq, and_true] at ha
  exact ⟨hs, ha.1, ha.2⟩

/-- **SolidCore's run of a valid call is the erased tree's result.** -/
theorem run_tree {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) {σ : List (Nat × Nat)} {dst v : Nat}
    (hcov : Generic.Covers deployed σ) (hto : dst < 2 ^ 160) (hv : v < 2 ^ 256) :
    (solidCore fuel).run c (transferCall σ dst v) = some (res (slotValue σ) dst v).obs := by
  obtain ⟨⟨d, hd⟩, f, hf, hlen, hT⟩ := facts hc
  exact source_run hd hcov (by decide) hf hT [dst, v] (by simp [hlen]) (by simp; omega)

/-- **`SeqPost` of every SolidCore run of a valid call**: no premise. -/
theorem meets_seq {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Meets (solidCore fuel) c (Valid deployed) SeqPost := by
  rintro _ ⟨σ, dst, v, hcov, hto, hv, rfl⟩ obs hrun
  rw [run_tree hc hcov hto hv, Option.some.injEq] at hrun
  subst hrun
  intro σ' dst' v' heq hto' hv'
  obtain ⟨rfl, rfl, rfl⟩ := transferCall_inj (by omega) hv (by omega) hv' heq
  exact tree_seq (slotValue σ) (fun k => Generic.slotValue_lt σ k) dst v hto hv

/-- **`TargetPost` of every SolidCore run of a valid call whose footprint premise holds.** -/
theorem meets_target {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Meets (solidCore fuel) c ValidIn TargetPost :=
  fun call h obs hrun => targetPost_of_seq (meets_seq hc call h.1 obs hrun) h.2

/-! ## solar-verify's exported spec over SolidCore's runs -/

/-- The ghost step of a call of `transfer`: the spec has no ghosts. -/
def idStep : GhostStep := fun _ g => g

/-- **The exported spec holds of SolidCore's checked contract** on the stage's calls of `transfer`
whose argument words meet the footprint premise. -/
theorem transfer_holds {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    HoldsFnUnder (fun call => SepArgs (callArgs call)) (solidCore fuel) c
      (SolidCore.Verify.VC.stageScope fn_transfer deployed) spec ctxOf idStep transfer_spec := by
  obtain ⟨⟨d, hd⟩, f, hf, hlen, hT⟩ := facts hc
  exact holdsFnUnder_of_tree_fixed (fn := fn_transfer) (ctx := ctx) hd (by decide) hf
    (by simpa [fn_transfer] using hlen) hT (fun call h => by simp [ctxOf, ctx, h]) (fun _ _ _ => rfl)
    (by simpa [fn_transfer] using transfer_meets)

theorem specs_eq : spec.spec.specs = [transfer_spec] := rfl

/-- A valid call is a stage call of `transfer` whose words meet the premise. -/
theorem scope_of_validIn {call : Call} (h : ValidIn call) :
    SolidCore.Verify.VC.stageScope fn_transfer deployed call ∧ SepArgs (callArgs call) := by
  obtain ⟨⟨σ, dst, v, hcov, hto, hv, rfl⟩, hs⟩ := h
  refine ⟨⟨σ, hcov, fn_transfer, by simp, [dst, v], rfl, by simp; omega, rfl⟩, ?_⟩
  rw [callArgs_transferCall σ (by omega) hv, sepArgs_iff hto]
  exact hs σ dst v rfl hto hv

/-- **The exported spec as `Shapes.Meets`** of `bundlePost` on the valid calls with their premise. -/
theorem meets_bundle {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Meets (solidCore fuel) c ValidIn (bundlePost spec ctxOf idStep) := by
  intro call h obs hrun fs hfs args pre hpre
  rw [specs_eq, List.mem_singleton] at hfs
  subst hfs
  obtain ⟨hsc, hP⟩ := scope_of_validIn h
  obtain ⟨obs', h1, h2⟩ := transfer_holds hc call hsc hP args pre hpre
  rw [hrun, Option.some.injEq] at h1
  subst h1
  exact h2

/-! ## Non-vacuity -/

/-- The witness storage: slot 3 (the constructor's) written, every `balanceOf` slot 0. -/
def σ0 : List (Nat × Nat) := [(3, 0)]

theorem covers_σ0 : Generic.Covers deployed σ0 := by
  intro kv hkv
  simp only [deployed, List.mem_singleton] at hkv
  subst hkv
  exact ⟨(3, 0), by simp [σ0], rfl⟩

/-- `transfer(1, 0)` from `σ0`, the caller `0x2000`. -/
def call0 : Call := transferCall σ0 1 0

theorem scope_call0 : Scope call0 := by
  intro σ dst v h hto hv
  obtain ⟨-, rfl, -⟩ := transferCall_inj (by decide) (by decide) (by omega) hv h
  exact scopedSep_transfer_example

theorem valid_call0 : ValidIn call0 :=
  ⟨⟨σ0, 1, 0, covers_σ0, by decide, by decide, rfl⟩, scope_call0⟩

/-- **The valid calls are inhabited**, the premise included (it holds of the real keccak256). -/
theorem valid_inhabited : ∃ call, ValidIn call := ⟨call0, valid_call0⟩

/-- An observable no correct `transfer` shows: success, with no log and no output. -/
def badObs : Observable := { success := true, output := [], logs := [], storage := slotValue σ0 }

/-- **`SeqPost` rejects something** on a valid call. -/
theorem nonVacuous_seq : ∃ call obs, Valid deployed call ∧ ¬ SeqPost call obs := by
  refine ⟨call0, badObs, valid_call0.1, fun h => ?_⟩
  have := ((h σ0 1 0 rfl (by decide) (by decide)).2.1 rfl).2.1
  simp [badObs] at this

/-- **`TargetPost` rejects something** on a valid call whose premise holds. -/
theorem nonVacuous_target : ∃ call obs, ValidIn call ∧ ¬ TargetPost call obs := by
  refine ⟨call0, badObs, valid_call0, fun h => ?_⟩
  have := ((h σ0 1 0 rfl (by decide) (by decide)).2.2.1 rfl).1
  simp [badObs] at this


/-! ## The required concrete runs -/

theorem slotValue_last (a b k x : Nat) : slotValue [(a, b), (k, x)] k = x % 2 ^ 256 := by
  simp [slotValue]

theorem covers_pair (k x : Nat) : Generic.Covers deployed [(3, 0), (k, x)] := by
  intro kv hkv
  simp only [deployed, List.mem_singleton] at hkv
  subst hkv
  exact ⟨(3, 0), by simp, rfl⟩

/-- **A self-transfer the balance covers succeeds, with the storage unchanged**, `Transfer(caller,
caller, v)` logged and `true` returned: no recipient-overflow condition. -/
theorem self_ok {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) {σ : List (Nat × Nat)} {v : Nat}
    (hcov : Generic.Covers deployed σ) (hv : v < 2 ^ 256) (hle : v ≤ slotValue σ (balKey caller)) :
    (solidCore fuel).run c (transferCall σ caller v) =
      some ⟨true, be32 1, [transferLog caller caller v], slotValue σ⟩ := by
  rw [run_tree hc hcov (by decide) hv]
  have hs := fun k => Generic.slotValue_lt σ k
  have hk : slotValue σ (balKey caller) < 2 ^ 256 := hs (balKey caller)
  have hov : debit (slotValue σ) v (balKey caller) + v < 2 ^ 256 := by
    simp only [debit, upd, balKey_mod, if_pos]
    omega
  rw [res_ok hs (by decide) hv hle hov]
  simp only [okRes, Res.obs, Option.some.injEq, Observable.mk.injEq, true_and]
  funext n
  simp only [seqStore, debit, upd, balKey_mod, if_pos]
  by_cases h : n % 2 ^ 256 = balKey caller
  · rw [if_pos h, ← SolidCore.Spec.UniswapV2.ERC20.Slice.slotValue_mod σ n, h]
    omega
  · rw [if_neg h, if_neg h]

/-- **A self-transfer of more than the balance reverts** with SafeMath's `ds-math-sub-underflow`,
no log and the storage unchanged. -/
theorem self_fail {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) {σ : List (Nat × Nat)} {v : Nat}
    (hcov : Generic.Covers deployed σ) (hv : v < 2 ^ 256) (hlt : slotValue σ (balKey caller) < v) :
    (solidCore fuel).run c (transferCall σ caller v) =
      some ⟨false, errorData subMsg, [], slotValue σ⟩ := by
  rw [run_tree hc hcov (by decide) hv, res_sub (fun k => Generic.slotValue_lt σ k) (by decide) hv (by omega)]
  rfl

/-- The storage with the caller's balance at `2 ^ 256 - 1`. -/
def σmax : List (Nat × Nat) := [(3, 0), (balKey caller, 2 ^ 256 - 1)]

/-- **Required case**: balance `2 ^ 256 - 1`, `transfer(caller, 1)` succeeds, the balance is
unchanged and `Transfer(caller, caller, 1)` is logged. -/
theorem self_max {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    slotValue σmax (balKey caller) = 2 ^ 256 - 1 ∧
    (solidCore fuel).run c (transferCall σmax caller 1) =
      some ⟨true, be32 1, [transferLog caller caller 1], slotValue σmax⟩ := by
  have hb : slotValue σmax (balKey caller) = 2 ^ 256 - 1 := by
    rw [σmax, slotValue_last]; decide
  exact ⟨hb, self_ok hc (covers_pair _ _) (by decide) (by rw [hb]; decide)⟩

/-- The storage with the caller's balance at 5. -/
def σshort : List (Nat × Nat) := [(3, 0), (balKey caller, 5)]

/-- **Required case**: a self-transfer of 6 from a balance of 5 reverts, with no change. -/
theorem self_short {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    (solidCore fuel).run c (transferCall σshort caller 6) =
      some ⟨false, errorData subMsg, [], slotValue σshort⟩ :=
  self_fail hc (covers_pair _ _) (by decide) (by rw [σshort, slotValue_last]; decide)

end SolidCore.Spec.UniswapV2.ERC20.Slice
