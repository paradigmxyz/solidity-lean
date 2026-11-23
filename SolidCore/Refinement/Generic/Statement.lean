import SolidCore.Refinement.Generic.StageFrom
import Verify.Lifecycle.Route
import Verify.Generic.Expected

/-!
# Constructor arguments: one constructor call for both statements

The generic source stage (`SolidCore.Refinement.Generic.StageFrom`, `Source.resultFromArgs?`) and the
lifecycle statement (`Verify.Lifecycle.Route`, `DeployedAtWith`) both run a contract after its
constructor. This module shows they run the same constructor call, so they cannot disagree on what
a deployment with argument words leaves:

* `deployArgs?_eq_lifecycle`, `deployedAtWith_eq`, `deployedAtWith_iff`: `Source.deployArgs?` is
  the call `DeployedAtWith` and `deployedAtWith` make on `wordArgs ws`, by `rfl`.
* `resultFromArgs?_of_deployedAtWith`: from the state a `DeployedAtWith` names, the generic
  run is the ABI dispatcher on exactly that state, with the call's storage written over it.
* `runFromArgs_eq_none`: a constructor that does not return (it reverts, or the words do not
  fit its parameters) leaves no run at all.

The argument words are bound to the creation code (`ArgsBound`): the creation code is the init
code followed by the ABI encoding of the words, 32 big-endian bytes each, so the words are what
`wordsOf` reads back from it (`ArgsBound.decode`) and no two lists of words fit the same creation
code (`ArgsBound.unique`). `Generic.Source.CreatedBy` states it of a source, and
`Generic.Source.run_of_statement` composes it with the lifecycle statement: the creation code
deploys the runtime code with the storage `s`, and in every runtime context the source semantics
runs from the state SolidCore's constructor left, whose storage is `s`.

The deployment frame is not the runtime frame: the constructor runs sent by `selfAddress` with no
value (`Wide.ctxOf`), whatever the call's caller and value, which reach only the dispatcher.

Not covered: dynamic argument types, a constructor that receives value, and the creation's
address derivation (as in `Verify.Lifecycle.Route`).
-/

namespace SolidCore.Refinement.Generic

open EthLib.Base SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement

/-! ## The constructor call -/

theorem deployArgs?_eq_lifecycle (fuel : Nat) (ws : List Nat) (c : TypeCheck.CheckedContract) :
    Refinement.Source.deployArgs? fuel ws c =
      TypeCheck.CheckedContract.constructWithContext? fuel c (Wide.ctxOf c) State.empty
        selfAddress 0 (Verify.Lifecycle.wordArgs ws) :=
  rfl

theorem deployedAtWith_eq (fuel : Nat) (ws : List Nat) (c : TypeCheck.CheckedContract)
    (s : List (Nat × Nat)) :
    Verify.Lifecycle.deployedAtWith fuel c (Verify.Lifecycle.wordArgs ws) s =
      match Refinement.Source.deployArgs? fuel ws c with
      | some (CallResult.returned d _) => d.storage.toList == s && d.events.isEmpty
      | _ => false :=
  rfl

theorem deployedAtWith_iff {fuel : Nat} {ws : List Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} :
    Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs ws) d s ↔
      (∃ vs, Refinement.Source.deployArgs? fuel ws c = some (CallResult.returned d vs)) ∧
        d.storage.toList = s ∧ d.events = [] :=
  ⟨fun h => ⟨h.cons, h.storage, h.events⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- From the state the lifecycle statement names, the generic run is the dispatcher on it. -/
theorem resultFromArgs?_of_deployedAtWith {fuel : Nat} {ws : List Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs ws) d s)
    (caller : Nat) (call : Call) :
    Refinement.Source.resultFromArgs? caller fuel ws c call =
      TypeCheck.CheckedContract.callCalldataAtFromWithContext? fuel c
        { c.core.context with sender := callerAddress, self := selfAddress, value := call.callvalue }
        { d with
          storage := call.storage.foldl
            (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage }
        selfAddress caller call.callvalue (call.calldata.data.toList.map (·.toNat)) := by
  obtain ⟨vs, hc⟩ := hd.cons
  have hc' : Refinement.Source.deployArgs? fuel ws c = some (CallResult.returned d vs) := hc
  simp only [Refinement.Source.resultFromArgs?, hc']

/-- A constructor that does not return leaves no run. -/
theorem runFromArgs_eq_none {fuel : Nat} {ws : List Nat} {c : TypeCheck.CheckedContract}
    (h : ∀ d vs, Refinement.Source.deployArgs? fuel ws c ≠ some (CallResult.returned d vs))
    (caller : Nat) (call : Call) : Refinement.Source.runFromArgs caller fuel ws c call = none := by
  unfold Refinement.Source.runFromArgs Refinement.Source.resultFromArgs?
  split
  next d vs hc => exact absurd hc (h d vs)
  next => rfl

/-! ## The words of the creation code -/

/-- The first `n` 32-byte big-endian words of `bs`. -/
def wordsOf : Nat → List UInt8 → List Nat
  | 0, _ => []
  | n + 1, bs => bytesToNat (bs.take 32) :: wordsOf n (bs.drop 32)

theorem argBytes_toList (ws : List Nat) :
    (Verify.Lifecycle.argBytes ws).data.toList = ws.flatMap fun w => natToBytes 32 w :=
  rfl

theorem wordsOf_flatMap (ws : List Nat) (h : ∀ w ∈ ws, w < 2 ^ 256) (rest : List UInt8) :
    wordsOf ws.length ((ws.flatMap fun w => natToBytes 32 w) ++ rest) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hw : w < 256 ^ 32 := by
      rw [show (256 : Nat) ^ 32 = 2 ^ 256 from rfl]; exact h w (List.mem_cons_self ..)
    have hl : (natToBytes 32 w).length = 32 := natToBytes_length 32 w
    simp only [List.flatMap_cons, List.length_cons, wordsOf, List.append_assoc]
    rw [List.take_left' hl, List.drop_left' hl, bytesToNat_natToBytes_of_lt hw,
      ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]

/-- **The argument words are the creation code's**: the creation code is the init code followed by
the ABI encoding of the words, and each word fits in 256 bits. -/
structure ArgsBound (initcode creation : ByteArray) (ws : List Nat) : Prop where
  code : creation = Verify.Lifecycle.initArgs initcode ws
  words : ∀ w ∈ ws, w < 2 ^ 256

theorem ArgsBound.size {initcode creation : ByteArray} {ws : List Nat}
    (h : ArgsBound initcode creation ws) : creation.size = initcode.size + 32 * ws.length := by
  rw [h.code, Verify.Lifecycle.initArgs, ByteArray.size_append, Verify.Lifecycle.argBytes_size]

/-- The words are read back from the creation code alone. -/
theorem ArgsBound.decode {initcode creation : ByteArray} {ws : List Nat}
    (h : ArgsBound initcode creation ws) :
    wordsOf ((creation.size - initcode.size) / 32) (creation.data.toList.drop initcode.size) =
      ws := by
  have hn : (creation.size - initcode.size) / 32 = ws.length := by rw [h.size]; omega
  rw [hn, h.code]
  have := wordsOf_flatMap ws h.words []
  rw [List.append_nil] at this
  simpa [Verify.Lifecycle.initArgs, argBytes_toList, ByteArray.data_append, Array.toList_append,
    List.drop_left' (show initcode.data.toList.length = initcode.size from rfl)] using this

/-- No two lists of words fit the same creation code. -/
theorem ArgsBound.unique {initcode creation : ByteArray} {ws ws' : List Nat}
    (h : ArgsBound initcode creation ws) (h' : ArgsBound initcode creation ws') : ws = ws' :=
  h.decode.symm.trans h'.decode

/-! ## Typed admission of the constructor's arguments

The first subset: a constructor that is not payable, whose parameters all have SolidCore type
`uint256` with no narrowing cleanup (narrow `uintN`, `intN` and enums lower to `uint256` or
`int256` with a cleanup; `address`, `bool`, `bytesN` and dynamic types are other types). Everything
else is refused, with the reason (`CtorBlocked`). The parameters are the checked contract's own
(`CheckedProgram.constructorFunctionFor?`, the lookup `constructWithContext?` makes) and the words are
decoded by SolidCore's own ABI decoder (`ABI.decodeFunctionArgs?`, the runtime dispatcher's).

Which layer refuses what: a suffix shorter than the parameters' heads is refused by the decoder
(its whole-head presence check) and by the exact suffix; trailing bytes after the heads, aligned
(an extra word) or not (a misaligned tail), are accepted by the decoder, as solc's is, and refused
only by the exact suffix (`ArgsBound.code`), so admission fails closed there. -/

/-- Why a constructor's arguments are not admitted. -/
inductive CtorBlocked where
  | noConstructor
  | payable
  | param (i : Nat) (ty : Solidity.Source.Ty)
  | cleanup (i : Nat) (k : Solidity.Source.AbiCleanup)
  | arity (params words : Nat)
  | wordRange
  | suffix
  | decode
  | decodeMismatch
  deriving Repr

/-- The word of a decoded value, if it is one. -/
def wordOf? : Solidity.Source.Value → Option Nat
  | .word w => some w
  | _ => none

/-- Every parameter type is `uint256`; else the first that is not. -/
def paramsOk : Nat → List Solidity.Source.Ty → Except CtorBlocked Unit
  | _, [] => .ok ()
  | i, .uint256 :: ts => paramsOk (i + 1) ts
  | i, t :: _ => .error (.param i t)

/-- Every parameter cleanup is none or `uint 256`; else the first that is not. -/
def cleanupsOk : Nat → List Solidity.Source.AbiCleanup → Except CtorBlocked Unit
  | _, [] => .ok ()
  | i, .none :: ks => cleanupsOk (i + 1) ks
  | i, .uint b :: ks => if b = 256 then cleanupsOk (i + 1) ks else .error (.cleanup i (.uint b))
  | i, k :: _ => .error (.cleanup i k)

/-- The bytes after the init code, as the decoder reads them. -/
def suffixBytes (initcode creation : ByteArray) : List Nat :=
  (creation.data.toList.drop initcode.size).map UInt8.toNat

/-- Admission against one constructor definition. -/
def admitFn (f : TypeCheck.CoreFunctionDef) (initcode creation : ByteArray) (ws : List Nat) :
    Except CtorBlocked Unit :=
  if f.payable then .error .payable else
  match paramsOk 0 (f.params.map Solidity.Source.BindingDecl.ty) with
  | .error e => .error e
  | .ok () =>
  match cleanupsOk 0 f.paramAbiCleanups with
  | .error e => .error e
  | .ok () =>
  if f.params.length ≠ ws.length then .error (.arity f.params.length ws.length) else
  if ¬ (∀ w ∈ ws, w < 2 ^ 256) then .error .wordRange else
  if creation.data.toList ≠ (Verify.Lifecycle.initArgs initcode ws).data.toList then .error .suffix else
  match Solidity.Source.ABI.decodeFunctionArgs? f (suffixBytes initcode creation) with
  | .error _ => .error .decode
  | .ok vs => if vs.map wordOf? = ws.map some then .ok () else .error .decodeMismatch

/-- **Typed admission**: the checked contract's constructor, its parameters in the subset, the
creation code exactly the init code and the words' encoding, and SolidCore's decoder reading back
exactly those words. -/
structure CtorAdmits (c : TypeCheck.CheckedContract) (initcode creation : ByteArray)
    (ws : List Nat) : Prop where
  bound : ArgsBound initcode creation ws
  ctor : ∃ f, TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl = some f ∧
    f.payable = false ∧
    f.params.map Solidity.Source.BindingDecl.ty = ws.map (fun _ => Solidity.Source.Ty.uint256) ∧
    (∀ k ∈ f.paramAbiCleanups, k = .none ∨ k = .uint 256) ∧
    Solidity.Source.ABI.decodeFunctionArgs? f (suffixBytes initcode creation) =
      .ok (Verify.Lifecycle.wordArgs ws)

/-- Admission of the checked contract's constructor: refused when there is none. -/
def admitCtor? (c : TypeCheck.CheckedContract) (initcode creation : ByteArray) (ws : List Nat) :
    Except CtorBlocked Unit :=
  match TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl with
  | none => .error .noConstructor
  | some f => admitFn f initcode creation ws

theorem paramsOk_sound : ∀ {i : Nat} {ts : List Solidity.Source.Ty}, paramsOk i ts = .ok () →
    ∀ t ∈ ts, t = .uint256
  | _, [], _ => by simp
  | i, t :: ts, h => by
    cases t <;> simp only [paramsOk, reduceCtorEq] at h
    intro t' ht'
    rcases List.mem_cons.mp ht' with rfl | ht'
    · rfl
    · exact paramsOk_sound h t' ht'

theorem cleanupsOk_sound : ∀ {i : Nat} {ks : List Solidity.Source.AbiCleanup},
    cleanupsOk i ks = .ok () → ∀ k ∈ ks, k = .none ∨ k = .uint 256
  | _, [], _ => by simp
  | i, k :: ks, h => by
    intro k' hk'
    cases k with
    | none =>
      simp only [cleanupsOk] at h
      rcases List.mem_cons.mp hk' with rfl | hk'
      · exact .inl rfl
      · exact cleanupsOk_sound h k' hk'
    | uint b =>
      simp only [cleanupsOk] at h
      split at h
      · next hb =>
        subst hb
        rcases List.mem_cons.mp hk' with rfl | hk'
        · exact .inr rfl
        · exact cleanupsOk_sound h k' hk'
      · simp at h
    | _ => simp [cleanupsOk] at h

theorem map_eq_of_mapWord : ∀ {vs : List Solidity.Source.Value} {ws : List Nat},
    vs.map wordOf? = ws.map some → vs = Verify.Lifecycle.wordArgs ws
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | v :: vs, w :: ws, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hv : v = .word w := by cases v <;> simp_all [wordOf?]
    simp only [Verify.Lifecycle.wordArgs, List.map_cons] at *
    rw [hv, map_eq_of_mapWord h2]; rfl

theorem map_uint256 {ts : List Solidity.Source.Ty} {ws : List Nat}
    (h : ∀ t ∈ ts, t = .uint256) (hl : ts.length = ws.length) :
    ts = ws.map (fun _ => Solidity.Source.Ty.uint256) := by
  induction ts generalizing ws with
  | nil => cases ws <;> simp_all
  | cons t ts ih =>
    cases ws with
    | nil => simp at hl
    | cons w ws =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨h t (List.mem_cons_self ..), ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
        (by simpa using hl)⟩

/-- **The checker is sound**: `admitCtor? = .ok ()` is checked evidence of `CtorAdmits`. -/
theorem admitCtor?_sound {c : TypeCheck.CheckedContract} {initcode creation : ByteArray}
    {ws : List Nat} (h : admitCtor? c initcode creation ws = .ok ()) :
    CtorAdmits c initcode creation ws := by
  unfold admitCtor? at h
  split at h
  · simp at h
  next f hf =>
  unfold admitFn at h
  split at h
  · simp at h
  next hpay =>
  split at h
  · simp at h
  next hp =>
  split at h
  · simp at h
  next hk =>
  split at h
  · simp at h
  next har =>
  split at h
  · simp at h
  next hwr =>
  split at h
  · simp at h
  next hsuf =>
  split at h
  · simp at h
  next vs hdec =>
  split at h
  · next hvs =>
    have hcode : creation = Verify.Lifecycle.initArgs initcode ws :=
      ByteArray.ext (Array.toList_inj.mp (Classical.not_not.mp hsuf))
    refine ⟨⟨hcode, Classical.not_not.mp hwr⟩, f, hf, by simpa using hpay, ?_, cleanupsOk_sound hk,
      by rw [hdec, map_eq_of_mapWord hvs]⟩
    exact map_uint256 (by simpa using paramsOk_sound hp)
      (by simpa using Classical.not_not.mp har)
  · simp at h

/-- No two lists of words are admitted for the same creation code. -/
theorem CtorAdmits.unique {c : TypeCheck.CheckedContract} {initcode creation : ByteArray}
    {ws ws' : List Nat} (h : CtorAdmits c initcode creation ws)
    (h' : CtorAdmits c initcode creation ws') : ws = ws' :=
  ArgsBound.unique h.bound h'.bound

end SolidCore.Refinement.Generic

namespace SolidCore.Verify.Generic

open SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic

/-- The source's argument words are the ones the creation code `creation` of `initcode` carries,
admitted for the checked contract `c`'s constructor (`CtorAdmits`): the exact suffix, the arity and the
typed values. -/
def Source.CreatedBy {ws : List Nat} (_ : Source ws) (c : TypeCheck.CheckedContract)
    (initcode creation : ByteArray) : Prop :=
  CtorAdmits c initcode creation ws

/-- Two sources created by the same creation code have the same argument words. -/
theorem Source.CreatedBy.unique {ws ws' : List Nat} {src : Source ws} {src' : Source ws'}
    {c : TypeCheck.CheckedContract} {initcode creation : ByteArray}
    (h : src.CreatedBy c initcode creation) (h' : src'.CreatedBy c initcode creation) :
    src.ctorArgs = src'.ctorArgs :=
  CtorAdmits.unique h h'

/-- **The lifecycle statement and the source semantics agree**: a source whose checked contract is
`c`, created by `creation` with its arguments admitted for `c`,
whose lifecycle statement holds, has its creation code deploy the runtime code `code` with the
storage `s`, and in every runtime context its semantics runs from the state SolidCore's constructor
left on the same words, whose storage is `s`. -/
theorem Source.run_of_statement {ws : List Nat} {src : Source ws} {c : TypeCheck.CheckedContract}
    {initcode code creation : ByteArray} {s : List (Nat × Nat)}
    (_hc : src.checked = .ok c)
    (hb : src.CreatedBy c initcode creation)
    (hl : Verify.Lifecycle.Statement src.fuel c initcode code ws s) :
    Deploys creation code s ∧ ∃ d : SolidCore.Solidity.Source.State, d.storage.toList = s ∧
      ∀ ctx : Context, ∀ call : Call, (src.semAt ctx).run c call =
        (TypeCheck.CheckedContract.callCalldataAtFromWithContext? src.fuel c
          { c.core.context with sender := callerAddress, self := selfAddress, value := call.callvalue }
          { d with
            storage := call.storage.foldl
              (fun acc kv => SolidCore.Solidity.Source.StorageMap.insertLoop acc kv.1 kv.2)
              d.storage }
          selfAddress ctx.caller call.callvalue (call.calldata.data.toList.map (·.toNat))).map
          (Refinement.Source.observe call) := by
  refine ⟨hb.bound.code ▸ hl.deploys, ?_⟩
  obtain ⟨d, hd⟩ := hl.source
  refine ⟨d, hd.storage, fun ctx call => ?_⟩
  show (Refinement.Source.resultFromArgs? ctx.caller src.fuel ws c call).map _ = _
  rw [resultFromArgs?_of_deployedAtWith hd]

end SolidCore.Verify.Generic
