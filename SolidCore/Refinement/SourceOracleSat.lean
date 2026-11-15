import SolidCore.Refinement.SourceOracle

/-!
# The oracle hypothesis is satisfiable

`callsAgree_sat`: an open world and a MIR oracle that agree (`CallsAgree`), so that a theorem with the
hypothesis `CallsAgree o W` is not vacuous for want of a world. In `failWorld` every external call that
is not to a precompile fails with empty return data and leaves the world as it was sent; a
precompile call is answered by SolidCore's precompile semantics, as every open world answers it;
no other account has code. `failOracle` computes the same answers from what the MIR frame sees of a
call (kind, callee, value, input), keeps the storage it had at the call, and reports no code.
-/

namespace SolidCore.Refinement

open SolidCore.Solidity SolidCore.Solidity.Source EvmCompiler.Simulation

namespace Witness

/-- The success flag and return data of a call in the failing world, from what both sides see of
it: a `STATICCALL` with no value to a precompile runs it, every other call fails with no data. -/
def failResp (k : SolarTV.Machine.CallKind) (callee value : Nat) (input : List Nat) : Bool × ByteArray :=
  if k = .staticcall ∧ value = 0 then
    match SolidCore.Solidity.Shared.Precompile.kindOfAddress? callee with
    | some kind =>
      match SolidCore.Solidity.Shared.Precompile.execute? kind input with
      | some (success, output) => (success, bytesToByteArray output)
      | none => (false, ByteArray.empty)
    | none => (false, ByteArray.empty)
  else (false, ByteArray.empty)

/-- The failing world's answer to a call: SolidCore's precompile answer, else a failure with no
data that leaves the sent world. -/
def failCall (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) : CallResponse :=
  (precompileAnswerCall? world request).getD
    { success := false, returnData := ByteArray.empty, postWorld := world,
      returnedGas := EvmYul.UInt256.ofNat 0 }

/-- The failing world's answerer. -/
def failAns : Ans := fun _ q =>
  match q with
  | .resource r => some (Query.defaultAnswer (.resource r))
  | .external world (.call request) => some (failCall world request)
  | .external world (.create request) => some (Query.defaultAnswer (.external world (.create request)))

/-- The failing world: `failAns`, and no other account has code. -/
def failWorld : World := { ans := failAns, codes := some [] }

theorem failCall_postWorld (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) :
    (failCall world request).postWorld = world := by
  unfold failCall precompileAnswerCall?
  repeat' split
  all_goals simp_all

theorem failCall_resp (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) :
    ((failCall world request).success, (failCall world request).returnData) =
      failResp (machineKind request.kind) (addressToWord request.codeAddress)
        (u256ToWord request.transferValue) (byteArrayToBytes request.calldata) := by
  unfold failCall precompileAnswerCall? failResp
  cases hk : request.kind <;> simp [machineKind]
  by_cases hv : u256ToWord request.transferValue = 0
  · simp only [hv, beq_self_eq_true, ↓reduceIte]
    cases SolidCore.Solidity.Shared.Precompile.kindOfAddress? (addressToWord request.codeAddress) with
    | none => rfl
    | some kind =>
      simp only
      cases SolidCore.Solidity.Shared.Precompile.execute? kind (byteArrayToBytes request.calldata) with
      | some r => rfl
      | none =>
        simp only
        split <;> rfl
  · simp [hv]

theorem failWorld_open : failWorld.Open where
  calls := by intros; rfl
  creates := by intros; rfl
  precompiles := by
    intro h world request a ha
    show some (failCall world request) = some a
    simp [failCall, ha]
  resources := by intros; rfl
  codes := rfl

/-- The failing oracle: the failing world's answers from the last call the frame made, the
storage it had at the call, no code at any address. -/
def failOracle : SolarTV.Machine.Oracle where
  env := fun name w args =>
    match name, args, (machineCalls w).getLast? with
    | "returndatasize", [], some (k, c, v, i) => BitVec.ofNat 256 (failResp k c v i).2.size
    | "returndata", [j], some (k, c, v, i) => BitVec.ofNat 256 ((failResp k c v i).2.get! j.toNat).toNat
    | _, _, _ => 0
  result := fun w =>
    match (machineCalls w).getLast? with
    | some (k, c, v, i) => if (failResp k c v i).1 then 1 else 0
    | none => 0
  storageAfter := fun w =>
    match w.getLast? with
    | some (.call _ _ _ st _) => st
    | _ => fun _ => 0
  transientAfter := fun w =>
    match w.getLast? with
    | some (.call _ _ _ _ tr) => tr
    | _ => fun _ => 0
  keccak := fun _ => 0
  caller := 0

theorem machineCalls_append (w rest : List SolarTV.Machine.Event) :
    machineCalls (w ++ rest) = machineCalls w ++ machineCalls rest := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    cases e <;> simp [machineCalls, ih]

theorem sourceCalls_append (h : List Interaction.Exchange) (e : Interaction.Exchange) :
    sourceCalls (h ++ [e]) = sourceCalls h ++ sourceCalls [e] := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    obtain ⟨q, a⟩ := x
    cases q with
    | resource r => simp [sourceCalls, ih]
    | external world req =>
      cases req <;> simp [sourceCalls, ih]

theorem failOracle_codes (w : List SolarTV.Machine.Event) (a : Nat) :
    failOracle.env "extcodesize" w [BitVec.ofNat 256 a] = 0 := by
  simp [failOracle]

/-- **The failing world and the failing oracle agree.** -/
theorem failAgree : CallsAgree failOracle failWorld where
  codes := by
    intro w _ a _
    simp [failOracle_codes, failWorld, SolidCore.Solidity.Shared.Account.codeAt,
      SolidCore.Solidity.Shared.Account.lookupBytes?]
  calls := by
    intro h world request a ha w k s i st tr hlast hm hst hcodes
    have ha' : a = failCall world request := by
      simp only [failWorld, failAns] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hresp := failCall_resp world request
    have hpost := failCall_postWorld world request
    have hl : (machineCalls w).getLast? = some (machineKind request.kind,
        addressToWord request.codeAddress, u256ToWord request.transferValue,
        byteArrayToBytes request.calldata) := by
      rw [hm, sourceCalls_append]
      simp [sourceCalls]
    refine ⟨?_, ?_, ?_⟩
    · simp only [SolarTV.Machine.callFlag, failOracle, hl]
      rw [Prod.ext_iff] at hresp
      rw [← hresp.1]
      cases (failCall world request).success <;> simp
    · intro _ slot hslot
      have := hst slot hslot
      simp only [failOracle, hlast, hpost]
      exact this
    · intro rest hrest
      have hl' : (machineCalls (w ++ rest)).getLast? = (machineCalls w).getLast? := by
        rw [machineCalls_append, hrest, List.append_nil]
      rw [Prod.ext_iff] at hresp
      refine ⟨?_, ?_, ?_⟩
      · simp only [SolarTV.Machine.returndataSize, failOracle, hl', hl, BitVec.toNat_ofNat]
        rw [← hresp.2]
      · intro j _ hj
        simp only [SolarTV.Machine.returndataByte, failOracle, hl', hl, ← hresp.2,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, BitVec.toNat_setWidth]
        have := ((failCall world request).returnData.get! j).toNat_lt
        omega
      · intro x hx
        have h0 := (hcodes x hx).mp (failOracle_codes _ _)
        simp only [failOracle_codes, true_iff]
        simpa [codeAfter, hpost] using h0
  static := by
    intro h world request a ha _ slot
    have ha' : a = failCall world request := by
      simp only [failWorld, failAns] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    rw [failCall_postWorld]
    exact ⟨rfl, rfl⟩

end Witness

/-- **The oracle hypothesis is satisfiable in the open world.** -/
theorem callsAgree_sat : ∃ (o : SolarTV.Machine.Oracle) (W : World), W.Open ∧ CallsAgree o W :=
  ⟨_, _, Witness.failWorld_open, Witness.failAgree⟩

/-- info: 'SolidCore.Refinement.callsAgree_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms callsAgree_sat

end SolidCore.Refinement
