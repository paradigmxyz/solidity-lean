import SolidCore.Verify.Abi

/-!
# Running a call from a given storage

The wide refinement proofs run SolidCore on calls from empty storage (`Wide.run_eq`). A
specification over a contract whose constructor leaves storage, such as c4's packed
`uint8 w = 7`, runs from that storage instead: on `callAt sel ws s`, the call of selector
`sel` on the free argument words `ws` from the storage `s`, which `Wide.run_eq_at` rewrites
to the ABI dispatcher of the core contract on the deployed state with `s` written over its
storage, for `src_symex` to evaluate. `callAt`, `deployedAt` and `run_eq_at` live in
`SolidCore.Refinement.Wide`, which the refinement proofs from a given storage share.

`implements_of_run` turns one theorem per function on free words into `Implements` on
`Abi.fullScope`. `vcs_of_fullScope` states the verification conditions on `Abi.fullScope`
call by call, with the argument words and the initial storage known, the form `sc_vcgen`
proves.
-/

namespace SolidCore.Verify

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source

/-- One theorem per function, on free argument words that meet `ok`, gives `Implements` on
the calls of `Abi.fullScope` whose argument words meet `ok`. -/
theorem implements_of_run {fuel : Nat} {c : TypeCheck.CheckedContract} {fns : List Fn}
    {s : List (Nat × Nat)} {n : Nat} {ok : List Nat → Prop} {model : List Nat → SolM (List Nat)}
    (hn : ∀ fn ∈ fns, fn.params.length = n)
    (h : ∀ fn ∈ fns, ∀ ws : List U256, ws.length = n → ok (ws.map BitVec.toNat) →
      Source.run fuel c (callAt fn.sel ws s) =
        some (observe (slotValue s) (model (ws.map BitVec.toNat) (slotValue s)))) :
    Implements fuel c (fun call => fullScope fns s call ∧ ok (argWords n call)) (argWords n)
      model := by
  rintro _ ⟨⟨fn, hfn, args, hlen, hargs, rfl⟩, hok⟩
  rw [hn fn hfn] at hlen
  have hw : argWords n ({ calldata := Abi.calldata fn.sel args, callvalue := 0, storage := s } :
      Call) = args := hlen ▸ argWords_calldata _ args hargs 0 s
  have hws := map_ofNat_toNat args hargs
  rw [hw] at hok ⊢
  have := h fn hfn (args.map (BitVec.ofNat 256)) (by simpa using hlen) (by rw [hws]; exact hok)
  rw [hws, ← callAt_of_args _ _ hargs] at this
  exact this

/-- `implements_of_run` with no condition on the argument words. -/
theorem implements_of_run' {fuel : Nat} {c : TypeCheck.CheckedContract} {fns : List Fn}
    {s : List (Nat × Nat)} {n : Nat} {model : List Nat → SolM (List Nat)}
    (hn : ∀ fn ∈ fns, fn.params.length = n)
    (h : ∀ fn ∈ fns, ∀ ws : List U256, ws.length = n →
      Source.run fuel c (callAt fn.sel ws s) =
        some (observe (slotValue s) (model (ws.map BitVec.toNat) (slotValue s)))) :
    Implements fuel c (fullScope fns s) (argWords n) model := fun call hs =>
  implements_of_run (ok := fun _ => True) hn (fun fn hfn ws hl _ => h fn hfn ws hl) call
    ⟨hs, trivial⟩

/-- `Implements` on a scope holds on every smaller one. -/
theorem Implements.mono {fuel : Nat} {c : TypeCheck.CheckedContract} {scope scope' : Call → Prop}
    {args : Call → List Nat} {model : List Nat → SolM (List Nat)}
    (h : Implements fuel c scope args model) (hs : ∀ call, scope' call → scope call) :
    Implements fuel c scope' args model := fun call hc => h call (hs call hc)

/-- The verification conditions on `Abi.fullScope`, call by call: for each function and each
list of argument words, with the call, its argument words and its initial storage known. -/
theorem vcs_of_fullScope {fns : List Fn} {s : List (Nat × Nat)} {n : Nat}
    {model : List Nat → SolM (List Nat)} {pre : Call → Prop} {post : Call → Observable → Prop}
    (hn : ∀ fn ∈ fns, fn.params.length = n)
    (h : ∀ fn ∈ fns, ∀ call args,
      call = ({ calldata := Abi.calldata fn.sel args, callvalue := 0, storage := s } : Call) →
      argWords n call = args → args.length = n → (∀ a ∈ args, a < 2 ^ 256) →
      initStorage call = slotValue s → pre call →
      wp (model args)
        (fun out _ s' => post call { success := true, output := out, logs := [], storage := s' })
        (fun e => post call { success := false, output := e, logs := [], storage := slotValue s })
        (slotValue s)) :
    ∀ call, fullScope fns s call → pre call → vc model (argWords n) post call := by
  rintro _ ⟨fn, hfn, args, hlen, hargs, rfl⟩ hpre
  rw [hn fn hfn] at hlen
  have hw : argWords n ({ calldata := Abi.calldata fn.sel args, callvalue := 0, storage := s } :
      Call) = args := hlen ▸ argWords_calldata _ args hargs 0 s
  have := h fn hfn _ args rfl hw hlen hargs rfl hpre
  simp only [vc, hw]
  exact this

/-- The verification conditions on a smaller scope follow from those on a larger one. -/
theorem vcs_mono {scope scope' pre : Call → Prop} {model : List Nat → SolM (List Nat)}
    {args : Call → List Nat} {post : Call → Observable → Prop}
    (h : ∀ call, scope call → pre call → vc model args post call)
    (hs : ∀ call, scope' call → scope call) :
    ∀ call, scope' call → pre call → vc model args post call := fun call hc hp =>
  h call (hs call hc) hp

/-- A slot of a storage map after the entries `σ` are written over it, as the last write of the
slot or the map's own entry. -/
theorem getElem?_foldl_insertLoop (σ : List (Nat × Nat)) (m0 : StorageMap) (q : Nat) :
    (σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) m0)[q]? =
      σ.foldl (fun acc kv => if Shared.norm kv.1 = q then some (Shared.norm kv.2) else acc)
        m0[q]? := by
  induction σ generalizing m0 with
  | nil => rfl
  | cons kv σ ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [StorageMap.insertLoop, Std.HashMap.getElem?_insert, beq_iff_eq]

/-- The last write of a slot among `σ`, as a word, is `slotValue`'s fold. -/
theorem getD_foldl (σ : List (Nat × Nat)) (k : Nat) (a : Option Nat) (b : Nat) (h : a.getD 0 = b) :
    (σ.foldl (fun acc kv => if Shared.norm kv.1 = k % 2 ^ 256 then some (Shared.norm kv.2) else acc)
      a).getD 0 =
      σ.foldl (fun acc kv => if kv.1 % 2 ^ 256 = k % 2 ^ 256 then kv.2 % 2 ^ 256 else acc) b := by
  induction σ generalizing a b with
  | nil => simpa using h
  | cons kv σ ih =>
    simp only [List.foldl_cons]
    apply ih
    simp only [Shared.norm, Shared.wordModulus, EvmYul.UInt256.size, Nat.reducePow]
    split <;> simp_all

/-- A slot of the storage a call writes over an empty deployed storage reads as `slotValue`. -/
theorem getD_storage {m0 : StorageMap} (h0 : ∀ q : Nat, m0[q]? = none) (σ : List (Nat × Nat))
    (k : Nat) :
    ((σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) m0)[k % 2 ^ 256]?).getD 0 =
      slotValue σ k := by
  rw [getElem?_foldl_insertLoop, h0]
  exact getD_foldl σ k none 0 rfl

/-- A constructor that leaves no storage leaves exactly the empty list of entries. -/
theorem deployedAt_of_deployed {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : Deployed fuel c d) : DeployedAt fuel c d [] :=
  ⟨hd.cons, by
    exact List.isEmpty_iff.mp (by rw [Std.HashMap.isEmpty_toList]; exact hd.storage), hd.events⟩

end SolidCore.Verify
