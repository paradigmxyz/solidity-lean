import SolidCore.Refinement.Generic.Statement

/-!
# Constructor arguments for every word

`decode_uint256_word`: SolidCore's own ABI decoder (`ABI.decodeFunctionArgs?`) reads back exactly
the words of their encoding, for a function whose parameters are all `uint256` with no narrowing
cleanup and for every list of words below `2 ^ 256`. `CtorAdmits.of_fn` turns that into typed
admission (Statement.lean) for every such list, from facts about the constructor alone, so a
contract's admission is proved once for all arguments instead of per pinned word.

`DeployedAtLoad` and `Source.run_of_load`: the lifecycle statement names the deployment by its
exact storage entry list (`Verify.Lifecycle.DeployedAtWith`). For a symbolic argument the generic
statement erasure (`SourceStmt`) gives only the deployed state's loads, which do not determine the
entry list of a hash map (a key written with 0 loads as an absent one). `DeployedAtLoad` is the
load-level deployment, and `Source.run_of_load` is `Source.run_of_statement`'s conclusion from it
and the bytecode's `Deploys`, so a constructor proved by erasure for every argument (Counter's
`counter_load_deployed`) reaches the same source-semantics statement.

A leaf: nothing imports it at its commit.
-/

namespace SolidCore.Refinement.Generic

open EthLib.Base SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement

/-! ## The decoder on uint256 words -/

/-- The suffix bytes of the words, as the decoder reads them. -/
def argData (ws : List Nat) : List Nat := (Verify.Lifecycle.argBytes ws).data.toList.map UInt8.toNat

theorem argData_eq (ws : List Nat) :
    argData ws = ws.flatMap fun w => (natToBytes 32 w).map UInt8.toNat := by
  simp [argData, argBytes_toList, List.map_flatMap]

theorem argData_append (p q : List Nat) : argData (p ++ q) = argData p ++ argData q := by
  simp [argData_eq, List.flatMap_append]

theorem argData_length (ws : List Nat) : (argData ws).length = 32 * ws.length := by
  rw [argData_eq]
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [List.flatMap_cons, natToBytes_length, ih]; omega

theorem normalizeBytes_toNat (l : List UInt8) :
    ABI.normalizeBytes (l.map UInt8.toNat) = l.map UInt8.toNat := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb : SolidCore.Solidity.Shared.External.byte b.toNat = b.toNat :=
      Nat.mod_eq_of_lt b.toNat_lt
    simp only [ABI.normalizeBytes, SolidCore.Solidity.Shared.External.normalizeBytes, List.map_cons,
      hb] at ih ⊢
    rw [ih]

theorem bytesToWordBE_toNat (l : List UInt8) :
    ABI.bytesToWordBE (l.map UInt8.toNat) = bytesToNat l % SolidCore.Solidity.Shared.wordModulus := by
  simp only [ABI.bytesToWordBE, SolidCore.Solidity.Shared.norm, bytesToNat, List.foldl_map,
    normByte, SolidCore.Solidity.Shared.Account.byte]
  congr 1
  congr 1
  funext acc b
  rw [Nat.mod_eq_of_lt b.toNat_lt]

/-- The word at head index `p.length` is `w`. -/
theorem readWord_at (p ws : List Nat) {w : Nat} (hw : w < 2 ^ 256) :
    ABI.readWord? (argData (p ++ w :: ws)) (ABI.wordBytes * p.length) = some w := by
  have hd : (argData (p ++ w :: ws)).drop (32 * p.length) =
      (natToBytes 32 w).map UInt8.toNat ++ argData ws := by
    rw [argData_append, List.drop_left' (by rw [argData_length])]
    simp [argData_eq, List.flatMap_cons]
  have hl : ((natToBytes 32 w).map UInt8.toNat).length = 32 := by simp [natToBytes_length]
  simp only [ABI.readWord?, ABI.readBytes?, ABI.wordBytes, hd]
  rw [if_pos (by simp only [List.length_append, hl]; omega)]
  simp only [List.take_left' hl, normalizeBytes_toNat, bytesToWordBE_toNat,
    bytesToNat_natToBytes_of_lt (show w < 256 ^ 32 from hw)]
  simp [Nat.mod_eq_of_lt (show w < SolidCore.Solidity.Shared.wordModulus from hw)]

theorem decodeArgsAux_uint256 (p ws : List Nat) (hw : ∀ w ∈ ws, w < 2 ^ 256) :
    ABI.decodeArgsAux? (argData (p ++ ws)) (ws.map fun _ => (true, Ty.uint256)) p.length =
      .ok (ws.map Value.word) := by
  induction ws generalizing p with
  | nil => rfl
  | cons w ws ih =>
    have hr := readWord_at p ws (hw w (List.mem_cons_self ..))
    have ih' := ih (p ++ [w]) (fun v hv => hw v (List.mem_cons_of_mem _ hv))
    simp only [List.append_assoc, List.singleton_append, List.length_append,
      List.length_singleton] at ih'
    have hv : ABI.decodeValueAt? true (argData (p ++ w :: ws)) p.length Ty.uint256 =
        .ok (Value.word w) := by
      simp only [ABI.decodeValueAt?, show ABI.Ty.abiDecodeFuel Ty.uint256 = 1 from rfl,
        ABI.decodeValueAtWithFuel?, hr, ABI.abiArgOpt]
      rfl
    have hh : ABI.Ty.abiHeadWords? Ty.uint256 = some 1 := rfl
    simp only [List.map_cons, ABI.decodeArgsAux?, hv, hh, ABI.abiArgOpt, bind, Except.bind]
    rw [ih']

theorem listAbiHeadWords_uint256 (ws : List Nat) :
    ABI.Ty.listAbiHeadWords? (ws.map fun _ => Ty.uint256) = some ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, ABI.Ty.listAbiHeadWords?, ih,
      show ABI.Ty.abiHeadWords? Ty.uint256 = some 1 from rfl]
    simp [bind, Option.bind]; omega

theorem zip_map_const {α β γ : Type} (ws : List α) (a : β) (b : γ) :
    (ws.map fun _ => a).zip (ws.map fun _ => b) = ws.map fun _ => (a, b) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.map_cons, List.zip_cons_cons, ih]

theorem lazyParamValues_uint256 : ∀ (ks : List AbiCleanup) (ws : List Nat),
    (∀ k ∈ ks, k = .none ∨ k = .uint 256) → ks.length = ws.length → (∀ w ∈ ws, w < 2 ^ 256) →
    AbiCleanups.lazyParamValues ks (ws.map Value.word) = some (ws.map Value.word)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | k :: ks, w :: ws, hk, hl, hw => by
    have ih := lazyParamValues_uint256 ks ws (fun k' hk' => hk k' (List.mem_cons_of_mem _ hk'))
      (by simpa using hl) (fun v hv => hw v (List.mem_cons_of_mem _ hv))
    have hwl : w < 2 ^ 256 := hw w (List.mem_cons_self ..)
    have hv : k.lazyParamValue (Value.word w) = some (Value.word w) := by
      rcases hk k (List.mem_cons_self ..) with rfl | rfl
      · rfl
      · have hwm : w < SolidCore.Solidity.Shared.wordModulus := hwl
        simp [AbiCleanup.lazyParamValue, AbiCleanup.accepts, SolidCore.Solidity.Shared.norm,
          Nat.mod_eq_of_lt hwm]
        exact hwl
    simp [List.map_cons, AbiCleanups.lazyParamValues, hv, ih, bind, Option.bind]

/-- **SolidCore's decoder reads back the words**, for a function whose parameters are all
`uint256` with no narrowing cleanup, and every list of words below `2 ^ 256`. -/
theorem decode_uint256_word (f : FunctionDef) (ws : List Nat)
    (hty : f.params.map BindingDecl.ty = ws.map fun _ => Ty.uint256)
    (hk : ∀ k ∈ f.paramAbiCleanups, k = .none ∨ k = .uint 256)
    (hkl : f.paramAbiCleanups = [] ∨ f.paramAbiCleanups.length = ws.length)
    (hw : ∀ w ∈ ws, w < 2 ^ 256) :
    ABI.decodeFunctionArgs? f (argData ws) = .ok (Verify.Lifecycle.wordArgs ws) := by
  have hlen : (f.params.map BindingDecl.ty).length = ws.length := by rw [hty]; simp
  have hflags : ((if f.paramAbiCleanups.length == (f.params.map BindingDecl.ty).length then
      f.paramAbiCleanups.map ABI.AbiCleanup.decodeLazy else (f.params.map BindingDecl.ty).map fun _ => true).zip
        (f.params.map BindingDecl.ty)) = ws.map fun _ => (true, Ty.uint256) := by
    rw [hty]
    split
    · rename_i h
      have hl : f.paramAbiCleanups.length = ws.length := by simpa using h
      have hlazy : f.paramAbiCleanups.map ABI.AbiCleanup.decodeLazy = ws.map fun _ => true := by
        apply List.ext_getElem (by simp [hl])
        intro i h1 h2
        simp only [List.getElem_map]
        rcases hk _ (List.getElem_mem (by simpa using h1)) with h | h <;> rw [h] <;> rfl
      rw [hlazy, zip_map_const]
    · rw [List.map_map]
      exact zip_map_const ws true Ty.uint256
  have hdec := decodeArgsAux_uint256 [] ws hw
  simp only [List.nil_append, List.length_nil] at hdec
  simp only [ABI.decodeFunctionArgs?, bind, Except.bind]
  rw [hflags]
  simp only [ABI.decodeArgsWith?, List.map_map, Function.comp_def, listAbiHeadWords_uint256,
    ABI.abiArgOpt, argData_length, bind, Except.bind, ABI.wordBytes]
  rw [if_neg (by omega), hdec]
  by_cases h0 : f.paramAbiCleanups = []
  · simp [h0, Verify.Lifecycle.wordArgs, pure, Except.pure]
  · simp [List.isEmpty_iff, h0, lazyParamValues_uint256 _ ws hk (hkl.resolve_left h0) hw,
      Verify.Lifecycle.wordArgs, pure, Except.pure]

/-! ## Typed admission for every word -/

/-- **Typed admission for every list of words**, from the constructor's shape alone: found,
not payable, every parameter `uint256` with no narrowing cleanup. -/
theorem CtorAdmits.of_fn {c : TypeCheck.CheckedContract} {f : FunctionDef} {initcode : ByteArray}
    {ws : List Nat}
    (hf : TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl = some f)
    (hpay : f.payable = false)
    (hty : f.params.map BindingDecl.ty = ws.map fun _ => Ty.uint256)
    (hk : ∀ k ∈ f.paramAbiCleanups, k = .none ∨ k = .uint 256)
    (hkl : f.paramAbiCleanups = [] ∨ f.paramAbiCleanups.length = ws.length)
    (hw : ∀ w ∈ ws, w < 2 ^ 256) :
    CtorAdmits c initcode (Verify.Lifecycle.initArgs initcode ws) ws := by
  have hsuf : suffixBytes initcode (Verify.Lifecycle.initArgs initcode ws) = argData ws := by
    simp only [suffixBytes, argData, Verify.Lifecycle.initArgs, ByteArray.data_append,
      Array.toList_append]
    rw [List.drop_left' (show initcode.data.toList.length = initcode.size from rfl)]
  exact ⟨⟨rfl, hw⟩, f, hf, hpay, hty, hk, by rw [hsuf]; exact decode_uint256_word f ws hty hk hkl hw⟩

/-! ## The deployment at the load level -/

/-- The value the entry list `s` gives slot `q`: its first entry's, else 0. -/
def slotOf (s : List (Nat × Nat)) (q : Nat) : Nat :=
  ((s.find? (fun kv => kv.1 == q)).map (·.2)).getD 0

/-- **The deployment at the load level**: SolidCore's constructor on the words returns a state with
no logs whose every slot loads what the entry list `s` gives it. -/
structure DeployedAtLoad (fuel : Nat) (c : TypeCheck.CheckedContract) (ws : List Nat)
    (s : List (Nat × Nat)) (d : Source.State) : Prop where
  cons : ∃ vs, Refinement.Source.deployArgs? fuel ws c = some (CallResult.returned d vs)
  events : d.events = []
  loads : ∀ k, k < 2 ^ 256 → d.loadSlot k = slotOf s k

/-- **The source-bytecode statement from a load-level deployment**: `Source.run_of_statement`'s
conclusion, with the source half named by its loads. -/
theorem Source.run_of_load {ws : List Nat} {src : SolidCore.Verify.Generic.Source ws}
    {c : TypeCheck.CheckedContract} {initcode code creation : ByteArray} {s : List (Nat × Nat)}
    {d : Source.State}
    (_hc : src.checked = .ok c)
    (hb : src.CreatedBy c initcode creation)
    (hdep : Deploys (Verify.Lifecycle.initArgs initcode ws) code s)
    (hd : DeployedAtLoad src.fuel c ws s d) :
    Deploys creation code s ∧ (∀ k, k < 2 ^ 256 → d.loadSlot k = slotOf s k) ∧
      ∀ ctx : SolidCore.Verify.Generic.Context, ∀ call : Call, (src.semAt ctx).run c call =
        (TypeCheck.CheckedContract.callCalldataAtFromWithContext? src.fuel c
          { c.core.context with sender := callerAddress, self := selfAddress, value := call.callvalue }
          { d with
            storage := call.storage.foldl
              (fun acc kv => SolidCore.Solidity.Source.StorageMap.insertLoop acc kv.1 kv.2)
              d.storage }
          selfAddress ctx.caller call.callvalue (call.calldata.data.toList.map (·.toNat))).map
          (Refinement.Source.observe call) := by
  refine ⟨hb.bound.code ▸ hdep, hd.loads, fun ctx call => ?_⟩
  obtain ⟨vs, hv⟩ := hd.cons
  show (Refinement.Source.resultFromArgs? ctx.caller src.fuel ws c call).map _ = _
  simp only [Refinement.Source.resultFromArgs?, hv]

end SolidCore.Refinement.Generic
