import SolidCore.Refinement.Wide.Source
import SolidCore.Refinement.Evm.WideStorage

/-!
# Refinement for functions with wide parameters

A corpus function with a `uint256`, `address`, `int256` or `bytes32` parameter has 2^256
argument words per parameter, so `Check.lean`'s evaluation of every call is out of
reach. Its refinement is proved one function at a time, symbolically on both sides:

1. SolidCore: `Wide.Tactic`'s `src_symex`, with the rules of `Wide.Source`
   (`wide_symex`), runs `Source.run` on the call `callOf sel ws` with free argument
   words `ws`. It splits on every condition on the words the interpreter meets and
   leaves, on each path, the goal that EthLib shows SolidCore's observable `X` there.
2. EthLib: `run_of_post` (`Evm.Wide`) reduces that goal to a frame specification,
   which `wide_tgt` proves by stepping solar's bytecode under the path's conditions.

This module holds what the per-contract proofs share: the context SolidCore's
`Source.result?` builds (`ctxOf`), the rewrite of `Source.run` on a call once the
constructor's result is known (`run_eq`), and `refines_of_calls`, which turns one
theorem per function into `Refines` on `Abi.fullScope`, every call of every function on
any argument words below `2 ^ 256`, from the storage SolidCore's constructor leaves: empty, or
the storage `deployedAt` checks, for `refines_of_calls_at`.

The per-contract facts a proof needs about SolidCore's checked contract, which comes
out of the type checker and so is opaque to the kernel, are checked once, in the kernel: that
its core contract is a literal the generator printed, and that its constructor leaves empty
storage, or the storage `deployedAt` names, and no logs, by one conversion check
(`kernel_rfl shape_eq`, `SolidCore.Refinement.KernelRfl`) on copies of the type checker that
read each function's selector from a table checked by Keccak-256 once per selector.
-/

namespace SolidCore.Refinement.Wide

open EthLib.Base SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement.Evm.Wide

/-- The context SolidCore's `Source.result?` calls the contract in. -/
def ctxOf (c : TypeCheck.CheckedContract) : Source.Context :=
  { c.core.context with sender := callerAddress, self := selfAddress, value := 0 }

/-- What the constructor of `c` leaves: the state `d`, with no storage and no logs. -/
structure Deployed (fuel : Nat) (c : TypeCheck.CheckedContract) (d : Source.State) : Prop where
  cons : ∃ vs, TypeCheck.CheckedContract.constructWithContext? fuel c (ctxOf c) State.empty
    selfAddress 0 [] = some (CallResult.returned d vs)
  storage : d.storage.isEmpty = true
  events : d.events = []

/-- Whether the constructor of `c` leaves no storage and no logs, as a `Bool`. -/
def deployedEmpty (fuel : Nat) (c : TypeCheck.CheckedContract) : Bool :=
  match TypeCheck.CheckedContract.constructWithContext? fuel c (ctxOf c) State.empty selfAddress
      0 [] with
  | some (CallResult.returned d _) => d.storage.isEmpty && d.events.isEmpty
  | _ => false

theorem deployed_of {fuel : Nat} {c : TypeCheck.CheckedContract}
    (h : deployedEmpty fuel c = true) : ∃ d, Deployed fuel c d := by
  unfold deployedEmpty at h
  split at h
  next d vs hc =>
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨d, ⟨vs, hc⟩, h.1, h.2⟩
  next => simp at h

theorem getElem?_of_isEmpty {m : Std.HashMap Nat Nat} (h : m.isEmpty = true) (k : Nat) :
    m[k]? = none :=
  Std.HashMap.getElem?_eq_none (Std.HashMap.isEmpty_iff_forall_not_mem.mp h _)

/-- `Source.run` of a call with empty storage, once the constructor's result is known: the
ABI dispatcher of the core contract on the call data, byte by byte. -/
theorem run_eq {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : Deployed fuel c d) (s : Nat) (ws : List U256) :
    Source.run fuel c (callOf s ws) =
      Option.map (Source.observe (callOf s ws))
        (ABI.Contract.callCalldataAtFromWithContext? fuel c.core (ctxOf c) d selfAddress
          callerAddress 0 ((natToBytes 4 s).map (·.toNat) ++ Dirty.argBytes (ws.map (·.toNat)))) := by
  obtain ⟨vs, hc⟩ := hd.cons
  simp only [Source.run, Source.result?, show (callOf s ws).callvalue = 0 from rfl,
    show (callOf s ws).storage = [] from rfl,
    show (callOf s ws).calldata = Abi.calldata s (ws.map (·.toNat)) from rfl]
  rw [show ({ c.core.context with sender := callerAddress, self := selfAddress, value := 0 } :
    Source.Context) = ctxOf c from rfl, hc]
  simp only [List.foldl_nil, TypeCheck.CheckedContract.callCalldataAtFromWithContext?,
    Dirty.bytes_calldata]

/-- One theorem per function, on free argument words, gives the refinement on every call of
every function on any argument words below `2 ^ 256`, from empty storage. -/
theorem refines_of_calls {fuel : Nat} {c : TypeCheck.CheckedContract} {code : ByteArray}
    {fns : List Abi.Fn}
    (h : ∀ fn ∈ fns, ∀ ws : List U256, ws.length = fn.params.length →
      ∃ obs, Source.run fuel c (callOf fn.sel ws) = some obs ∧
        Target.run code (callOf fn.sel ws) = some obs) :
    Refines fuel c code (Abi.fullScope fns []) := by
  rintro _ ⟨fn, hfn, args, hlen, hargs, rfl⟩
  have hws : (args.map (BitVec.ofNat 256)).map BitVec.toNat = args := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id args]
    apply List.map_congr_left
    intro a ha
    simpa using hargs a ha
  have := h fn hfn (args.map (BitVec.ofNat 256)) (by simpa using hlen)
  simp only [callOf, hws] at this
  exact this

/-! ## Calls from the storage the constructor leaves

A constructor that leaves storage `s` makes every call of `Abi.fullScope fns s` start from it:
`callAt sel ws s` (`Evm.Wide`). `deployedAt` checks what the constructor leaves, `run_eq_at`
rewrites `Source.run` of such a call as `run_eq` does from empty storage, and
`refines_of_calls_at` is `refines_of_calls` from `s`. -/

/-- What the constructor of `c` leaves: the state `d`, whose storage holds exactly the
entries `s`, with no logs. -/
structure DeployedAt (fuel : Nat) (c : TypeCheck.CheckedContract) (d : Source.State)
    (s : List (Nat × Nat)) : Prop where
  cons : ∃ vs, TypeCheck.CheckedContract.constructWithContext? fuel c (ctxOf c) State.empty
    selfAddress 0 [] = some (CallResult.returned d vs)
  storage : d.storage.toList = s
  events : d.events = []

/-- Whether the constructor of `c` leaves exactly the storage entries `s` and no logs. -/
def deployedAt (fuel : Nat) (c : TypeCheck.CheckedContract) (s : List (Nat × Nat)) : Bool :=
  match TypeCheck.CheckedContract.constructWithContext? fuel c (ctxOf c) State.empty selfAddress
      0 [] with
  | some (CallResult.returned d _) => d.storage.toList == s && d.events.isEmpty
  | _ => false

theorem deployedAt_of {fuel : Nat} {c : TypeCheck.CheckedContract} {s : List (Nat × Nat)}
    (h : deployedAt fuel c s = true) : ∃ d, DeployedAt fuel c d s := by
  unfold deployedAt at h
  split at h
  next d vs hc =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    exact ⟨d, ⟨vs, hc⟩, h.1, h.2⟩
  next => simp at h

/-- A slot the deployed storage has no entry for reads as none. -/
theorem DeployedAt.getElem?_eq_none {fuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : DeployedAt fuel c d s) {k : Nat}
    (hk : ∀ v, (k, v) ∉ s) : d.storage[k]? = none := by
  rcases h : d.storage[k]? with _ | v
  · rfl
  · exact absurd (hd.storage ▸ Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h) (hk v)

/-- A lookup after an insert, for the evaluator. -/
theorem get?_insert (m : Std.HashMap Nat Nat) (k v q : Nat) :
    (m.insert k v).get? q = if k = q then some v else m.get? q := by
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq]

/-- `Source.run` of a call from the storage `σ`, once the constructor's result is known:
the ABI dispatcher of the core contract on the call data, from the deployed state with `σ`
written over its storage. -/
theorem run_eq_at {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : DeployedAt fuel c d s) (sel : Nat) (ws : List U256)
    (σ : List (Nat × Nat)) :
    Source.run fuel c (callAt sel ws σ) =
      Option.map (Source.observe (callAt sel ws σ))
        (ABI.Contract.callCalldataAtFromWithContext? fuel c.core (ctxOf c)
          { d with storage := σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage }
          selfAddress callerAddress 0
          ((natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes (ws.map (·.toNat)))) := by
  obtain ⟨vs, hc⟩ := hd.cons
  simp only [Source.run, Source.result?, show (callAt sel ws σ).callvalue = 0 from rfl,
    show (callAt sel ws σ).storage = σ from rfl,
    show (callAt sel ws σ).calldata = Abi.calldata sel (ws.map (·.toNat)) from rfl]
  rw [show ({ c.core.context with sender := callerAddress, self := selfAddress, value := 0 } :
    Source.Context) = ctxOf c from rfl, hc]
  simp only [TypeCheck.CheckedContract.callCalldataAtFromWithContext?, Dirty.bytes_calldata]

/-- `Source.runFrom caller` of a call from the storage `σ`, once the constructor's result is
known: `run_eq_at` with the dispatcher called from `caller`. -/
theorem run_eq_atFrom (caller : Nat) {fuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : DeployedAt fuel c d s) (sel : Nat)
    (ws : List U256) (σ : List (Nat × Nat)) :
    Source.runFrom caller fuel c (callAt sel ws σ) =
      Option.map (Source.observe (callAt sel ws σ))
        (ABI.Contract.callCalldataAtFromWithContext? fuel c.core (ctxOf c)
          { d with storage := σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage }
          selfAddress caller 0
          ((natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes (ws.map (·.toNat)))) := by
  obtain ⟨vs, hc⟩ := hd.cons
  simp only [Source.runFrom, Source.resultFrom?, show (callAt sel ws σ).callvalue = 0 from rfl,
    show (callAt sel ws σ).storage = σ from rfl,
    show (callAt sel ws σ).calldata = Abi.calldata sel (ws.map (·.toNat)) from rfl]
  rw [show ({ c.core.context with sender := callerAddress, self := selfAddress, value := 0 } :
    Source.Context) = ctxOf c from rfl, hc]
  simp only [TypeCheck.CheckedContract.callCalldataAtFromWithContext?, Dirty.bytes_calldata]

theorem map_ofNat_toNat (args : List Nat) (hargs : ∀ a ∈ args, a < 2 ^ 256) :
    (args.map (BitVec.ofNat 256)).map BitVec.toNat = args := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id args]
  apply List.map_congr_left
  intro a ha
  simpa using Nat.mod_eq_of_lt (hargs a ha)

/-- A call of `Abi.fullScope` is `callAt` of its argument words. -/
theorem callAt_of_args (sel : Nat) (args : List Nat) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (s : List (Nat × Nat)) :
    ({ calldata := Abi.calldata sel args, callvalue := 0, storage := s } : Call) =
      callAt sel (args.map (BitVec.ofNat 256)) s := by
  simp only [callAt, map_ofNat_toNat args hargs]

/-- One theorem per function on free argument words, from the storage `s`, gives the refinement
on every call of every function on any argument words below `2 ^ 256`, from `s`. -/
theorem refines_of_calls_at {fuel : Nat} {c : TypeCheck.CheckedContract} {code : ByteArray}
    {fns : List Abi.Fn} {s : List (Nat × Nat)}
    (h : ∀ fn ∈ fns, ∀ ws : List U256, ws.length = fn.params.length →
      ∃ obs, Source.run fuel c (callAt fn.sel ws s) = some obs ∧
        Target.run code (callAt fn.sel ws s) = some obs) :
    Refines fuel c code (Abi.fullScope fns s) := by
  rintro _ ⟨fn, hfn, args, hlen, hargs, rfl⟩
  rw [callAt_of_args _ _ hargs]
  exact h fn hfn _ (by simpa using hlen)

end SolidCore.Refinement.Wide
