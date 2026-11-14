import SolidCore.Refinement.Solar.AssembleCut
import SolidCore.Refinement.SourceOracleSat

/-!
# An open world whose static calls succeed, from a run's table

`AssembleCut.O_agree` meets the oracle hypothesis (`CallsAgree`) with `Witness.failWorld`, in which
every call to code fails. Here the open world `tabWorld oks outs codes` answers the `n`-th call of a
source history, when it is a `STATICCALL` to code (not to a precompile address), with the table's
`n`-th success flag and return data, leaving the world it was sent (a static frame keeps every
account, as `AssembleCall.meets_static` proves of EthLib's runner); a precompile call is answered by
SolidCore's precompile semantics, as every open world answers it; every other call fails, leaving the
sent world. The other accounts' code is `codes`, read before and after calls.

`tabOracle` computes the same answers from what the MIR frame sees of its calls (kind, callee, value,
input, and their number), and `tabAgree` proves the two agree. `OS codes T` is the oracle of a run's
table `T` (its GAS reads and the flags and return data of its static calls) over EthLib's caller,
hash and environment: `OS_agree` gives the open world for it and `OS_ok` the certificate's
constraints, the two premises `SourceOracle.holds_of_runs` asks of the oracle of a run once the
checker cuts at STATICCALL.
-/

namespace SolidCore.Refinement

open SolidCore.Solidity SolidCore.Solidity.Source EvmCompiler.Simulation

namespace Witness

/-- A `STATICCALL`, on the MIR side. -/
def isStaticM : SolarTV.Machine.CallKind → Bool
  | .staticcall => true
  | _ => false

/-- A `STATICCALL`, on the source side. -/
def isStaticS : CallKind → Bool
  | .staticcall => true
  | _ => false

theorem isStaticM_machineKind (k : CallKind) : isStaticM (machineKind k) = isStaticS k := by
  cases k <;> rfl

/-- A `STATICCALL` with no value to a precompile address, which SolidCore answers itself. -/
def prePath (k : SolarTV.Machine.CallKind) (callee value : Nat) : Bool :=
  isStaticM k && value == 0 && (SolidCore.Solidity.Shared.Precompile.kindOfAddress? callee).isSome

/-- A static call to code: answered by the table. -/
def toCode (k : SolarTV.Machine.CallKind) (callee value : Nat) : Bool :=
  isStaticM k && !prePath k callee value

/-- The success flag and return data of the `n`-th call in the table's world, from what both sides
see of it. -/
def tabResp (oks : List Bool) (outs : List ByteArray) (n : Nat) (k : SolarTV.Machine.CallKind)
    (callee value : Nat) (input : List Nat) : Bool × ByteArray :=
  if toCode k callee value then (oks.getD n false, outs.getD n ByteArray.empty)
  else failResp k callee value input

/-- The table's answer to its `n`-th call, a static call to code: the table's flag and return data,
and the world it was sent. -/
def tabHit (oks : List Bool) (outs : List ByteArray) (n : Nat)
    (world : SolidCore.Solidity.Shared.OpenWorld) : CallResponse :=
  { success := oks.getD n false, returnData := outs.getD n ByteArray.empty, postWorld := world,
    returnedGas := EvmYul.UInt256.ofNat 0 }

/-- The table's world's answer to its `n`-th call. -/
def tabCall (oks : List Bool) (outs : List ByteArray) (n : Nat)
    (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) : CallResponse :=
  if toCode (machineKind request.kind) (addressToWord request.codeAddress)
      (u256ToWord request.transferValue) then tabHit oks outs n world
  else failCall world request

/-- The table's world's answerer: the `n`-th external call of a history is answered by `tabCall`
with `n` the number of calls before it. -/
def tabAns (oks : List Bool) (outs : List ByteArray) : Ans := fun h q =>
  match q with
  | .resource r => some (Query.defaultAnswer (.resource r))
  | .external world (.call request) => some (tabCall oks outs (sourceCalls h).length world request)
  | .external world (.create request) => some (Query.defaultAnswer (.external world (.create request)))

/-- The table's world, with `codes` the other accounts' code. -/
def tabWorld (oks : List Bool) (outs : List ByteArray) (codes : Shared.Account.BytesMap) : World :=
  { ans := tabAns oks outs, codes := some codes }

/-- A precompile answer comes only from a static call with no value to a precompile address. -/
theorem prePath_of_answer {world : SolidCore.Solidity.Shared.OpenWorld} {request : CallRequest}
    {a : CallResponse} (h : precompileAnswerCall? world request = some a) :
    prePath (machineKind request.kind) (addressToWord request.codeAddress)
      (u256ToWord request.transferValue) = true := by
  unfold precompileAnswerCall? at h
  cases hk : request.kind <;> simp only [hk] at h <;> try cases h
  by_cases hv : u256ToWord request.transferValue = 0
  · cases ho : SolidCore.Solidity.Shared.Precompile.kindOfAddress? (addressToWord request.codeAddress) with
    | none => simp [hv, ho] at h
    | some kind => simp [prePath, machineKind, isStaticM, hv, ho]
  · simp [hv] at h

theorem tabCall_postWorld (oks : List Bool) (outs : List ByteArray) (n : Nat)
    (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) :
    (tabCall oks outs n world request).postWorld = world := by
  unfold tabCall
  split
  · rfl
  · exact failCall_postWorld world request

theorem tabCall_resp (oks : List Bool) (outs : List ByteArray) (n : Nat)
    (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) :
    ((tabCall oks outs n world request).success, (tabCall oks outs n world request).returnData) =
      tabResp oks outs n (machineKind request.kind) (addressToWord request.codeAddress)
        (u256ToWord request.transferValue) (byteArrayToBytes request.calldata) := by
  unfold tabCall tabResp
  split
  · rfl
  · exact failCall_resp world request

/-- **The table's world is a world of the open world.** -/
theorem tabWorld_open (oks : List Bool) (outs : List ByteArray) (codes : Shared.Account.BytesMap) :
    (tabWorld oks outs codes).Open where
  calls := by intros; rfl
  creates := by intros; rfl
  precompiles := by
    intro h world request a ha
    show some (tabCall oks outs (sourceCalls h).length world request) = some a
    have hp := prePath_of_answer ha
    simp [tabCall, toCode, hp, failCall, ha]
  resources := by intros; rfl
  codes := rfl

/-- The reads of the table's oracle: the return data of the frame's last call, the table's
world's, and `codes`' code test at every address. -/
def tabEnv (oks : List Bool) (outs : List ByteArray) (codes : Shared.Account.BytesMap)
    (name : String) (w : List SolarTV.Machine.Event) (args : List (BitVec 256)) : BitVec 256 :=
  if name = "extcodesize" then
    match args with
    | [a] => if (Shared.Account.codeAt codes a.toNat).isEmpty then 0 else 1
    | _ => 0
  else
    match name, args, (machineCalls w).getLast? with
    | "returndatasize", [], some (k, c, v, i) =>
      BitVec.ofNat 256 (tabResp oks outs ((machineCalls w).length - 1) k c v i).2.size
    | "returndata", [j], some (k, c, v, i) =>
      BitVec.ofNat 256 ((tabResp oks outs ((machineCalls w).length - 1) k c v i).2.get! j.toNat).toNat
    | _, _, _ => 0

/-- The success flag of the frame's last call, the table's world's. -/
def tabResult (oks : List Bool) (outs : List ByteArray) (w : List SolarTV.Machine.Event) : BitVec 256 :=
  match (machineCalls w).getLast? with
  | some (k, c, v, i) => if (tabResp oks outs ((machineCalls w).length - 1) k c v i).1 then 1 else 0
  | none => 0

/-- The table's oracle: the table's world's answers from the frame's last call and the number of
its calls, the storage it had at the call, and `codes`' code test at every address. -/
def tabOracle (oks : List Bool) (outs : List ByteArray) (codes : Shared.Account.BytesMap) :
    SolarTV.Machine.Oracle where
  env := tabEnv oks outs codes
  result := tabResult oks outs
  storageAfter := failOracle.storageAfter
  transientAfter := failOracle.transientAfter
  keccak := fun _ => 0
  caller := 0

theorem tabOracle_envEq (oks : List Bool) (outs : List ByteArray) (codes : Shared.Account.BytesMap) :
    (tabOracle oks outs codes).env = tabEnv oks outs codes := rfl

theorem tabOracle_codes (oks : List Bool) (outs : List ByteArray) (codes : Shared.Account.BytesMap)
    (w : List SolarTV.Machine.Event) (a : Nat) :
    (tabOracle oks outs codes).env "extcodesize" w [BitVec.ofNat 256 a] =
      if (Shared.Account.codeAt codes (a % 2 ^ 256)).isEmpty then 0 else 1 := by
  rw [tabOracle_envEq]
  simp [tabEnv]

/-- The table oracle's code test does not depend on the world. -/
theorem tabOracle_codesAgree {oks : List Bool} {outs : List ByteArray}
    {codes : Shared.Account.BytesMap} {w w' : List SolarTV.Machine.Event}
    {code : Nat → List SolidCore.Solidity.Byte} (h : CodesAgree (tabOracle oks outs codes) w code) :
    CodesAgree (tabOracle oks outs codes) w' code := by
  intro a ha
  rw [tabOracle_codes]
  have := h a ha
  rwa [tabOracle_codes] at this

/-- **The table's world and the table's oracle agree.** -/
theorem tabAgree (oks : List Bool) (outs : List ByteArray) (codes : Shared.Account.BytesMap) :
    CallsAgree (tabOracle oks outs codes) (tabWorld oks outs codes) where
  codes := by
    intro w _ a ha
    rw [tabOracle_codes, Nat.mod_eq_of_lt (by omega)]
    simp only [tabWorld, Option.getD_some]
    split <;> simp_all
  calls := by
    intro h world request a ha w k s i st tr hlast hm hst hcodes
    have ha' : a = tabCall oks outs (sourceCalls h).length world request := by
      simp only [tabWorld, tabAns] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hresp := tabCall_resp oks outs (sourceCalls h).length world request
    have hpost := tabCall_postWorld oks outs (sourceCalls h).length world request
    have hm' : machineCalls w = sourceCalls h ++ [(machineKind request.kind,
        addressToWord request.codeAddress, u256ToWord request.transferValue,
        byteArrayToBytes request.calldata)] := by
      rw [hm, sourceCalls_append]
      simp [sourceCalls]
    have hl : (machineCalls w).getLast? = some (machineKind request.kind,
        addressToWord request.codeAddress, u256ToWord request.transferValue,
        byteArrayToBytes request.calldata) := by
      rw [hm']
      simp
    have hn : (machineCalls w).length - 1 = (sourceCalls h).length := by
      rw [hm']
      simp
    refine ⟨?_, ?_, ?_⟩
    · simp only [SolarTV.Machine.callFlag]
      show (if tabResult oks outs w = 0 then _ else _) = _ ↔ _
      simp only [tabResult, hl, hn]
      rw [Prod.ext_iff] at hresp
      rw [← hresp.1]
      cases (tabCall oks outs (sourceCalls h).length world request).success <;> simp
    · intro _ slot hslot
      have := hst slot hslot
      show ((failOracle.storageAfter w) _).toNat = _ ∧ ((failOracle.transientAfter w) _).toNat = _
      simp only [failOracle, hlast, hpost]
      exact this
    · intro rest hrest
      have hmr : machineCalls (w ++ rest) = machineCalls w := by
        rw [machineCalls_append, hrest, List.append_nil]
      rw [Prod.ext_iff] at hresp
      refine ⟨?_, ?_, ?_⟩
      · simp only [SolarTV.Machine.returndataSize]
        rw [tabOracle_envEq]
        simp only [tabEnv, show ("returndatasize" = "extcodesize") = False by simp, ite_false, hmr, hl, hn, BitVec.toNat_ofNat]
        rw [← hresp.2]
      · intro j _ hj
        simp only [SolarTV.Machine.returndataByte]
        rw [tabOracle_envEq]
        simp only [tabEnv, show ("returndata" = "extcodesize") = False by simp, ite_false, hmr, hl, hn, ← hresp.2,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, BitVec.toNat_setWidth]
        have := ((tabCall oks outs (sourceCalls h).length world request).returnData.get! j).toNat_lt
        omega
      · have hc := tabOracle_codesAgree (w' := w ++ rest) hcodes
        have hca : codeAfter (tabWorld oks outs codes)
            (h ++ [⟨.external world (.call request), tabCall oks outs (sourceCalls h).length world request⟩])
            = codeIn world := by
          funext x
          simp [codeAfter, hpost]
        rw [hca]
        exact hc
  static := by
    intro h world request a ha _ slot
    have ha' : a = tabCall oks outs (sourceCalls h).length world request := by
      simp only [tabWorld, tabAns] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    rw [tabCall_postWorld]
    exact ⟨rfl, rfl⟩

/-- In the table's world a static call to code succeeds exactly as the table says, with the table's
return data. -/
theorem tabWorld_static (oks : List Bool) (outs : List ByteArray) (codes : Shared.Account.BytesMap)
    (h : List Interaction.Exchange) (world : SolidCore.Solidity.Shared.OpenWorld)
    (request : CallRequest)
    (hc : toCode (machineKind request.kind) (addressToWord request.codeAddress)
      (u256ToWord request.transferValue) = true) :
    (tabWorld oks outs codes).ans h (.external world (.call request)) =
      some (tabHit oks outs (sourceCalls h).length world) := by
  simp only [tabWorld, tabAns, tabCall, hc, ite_true]
  rfl

end Witness

end SolidCore.Refinement

namespace SolidCore.Refinement.Solar.AssembleCallWorld

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Witness
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleCut SolidCore.Refinement.Solar.AssembleEffects
open SolidCore.Solidity SolidCore.Solidity.Source EvmCompiler.Simulation

/-- **The oracle of a run that makes static calls**: GAS reads from the table's `gases`, EthLib's
caller, hash and environment, and the success flags and return data of its static calls to code from
the table's `oks` and `outs`, in order; `codes` is the other accounts' code. -/
abbrev OS (codes : SolidCore.Solidity.Shared.Account.BytesMap) (T : RunTable) : Oracle :=
  gasOracle (envOracle (ethOracle (tabOracle T.oks T.outs codes))) T

theorem OS_ok (codes : SolidCore.Solidity.Shared.Account.BytesMap) (c : Cert) (T : RunTable) :
    CertOk c (OS codes T) := by
  refine ⟨fun _ => ethOracle_ok (tabOracle T.oks T.outs codes), fun _ => ?_⟩
  intro name byte w he world
  have hn : name ≠ "gas" := by
    unfold envRead at he
    rintro rfl
    simp at he
  simp only [OS, gasOracle, hn, false_and, ite_false]
  exact envOracle_ok _ name byte w he world

/-- **The open world of a run that makes static calls**: the oracle of every table agrees with the
table's world, in which the table's static calls to code succeed or fail as the table says, with its
return data. This replaces `AssembleCut.O_agree`'s world, in which every call to code fails. -/
theorem OS_agree (codes : SolidCore.Solidity.Shared.Account.BytesMap) (T : RunTable) :
    (tabWorld T.oks T.outs codes).Open ∧ CallsAgree (OS codes T) (tabWorld T.oks T.outs codes) :=
  ⟨tabWorld_open _ _ _, callsAgree_gas T (callsAgree_envEth (tabAgree _ _ _))⟩

/-! ## A static call to code under the oracle of a run -/

theorem OS_env (codes : SolidCore.Solidity.Shared.Account.BytesMap) (T : RunTable) (n : String)
    (w : List SolarTV.Machine.Event) (a : List (BitVec 256)) (hn : n ≠ "gas") (h : envRead n = none) :
    (OS codes T).env n w a = tabEnv T.oks T.outs codes n w a := by
  simp only [OS, gasOracle, hn, false_and, ite_false]
  rw [env_envEth _ n w a h]
  rfl

theorem data_getElem! (b : ByteArray) (i : Nat) (h : i < b.size) : b.data[i]! = b[i] := by
  rw [getElem!_pos b.data i (by simpa using h)]
  rfl

theorem machineCalls_static (w : List SolarTV.Machine.Event) (gas addr : (BitVec 256)) (input : List SolarTV.Memory.Byte)
    (st tr : (BitVec 256) → (BitVec 256)) :
    machineCalls (w ++ [.call .staticcall [gas, addr] input st tr]) =
      machineCalls w ++ [(.staticcall, addr.toNat % 2 ^ 160, 0, input.map BitVec.toNat)] := by
  rw [machineCalls_append]
  simp [machineCalls]

/-- **A static call to code under the oracle of a run answers the table's next entry**: the
`n`-th call of the frame (`n` the calls before it) succeeds as the table's `n`-th flag says, and
until the next call the return data is the table's `n`-th output. With
`AssembleCall.staticcall_back`, which reads the callee frame's flag and output from the run, these
are `AssembleCall.staticcall_effectW`'s premises. -/
theorem OS_static (codes : SolidCore.Solidity.Shared.Account.BytesMap) (T : RunTable)
    (w : List SolarTV.Machine.Event) (gas addr : (BitVec 256)) (input : List SolarTV.Memory.Byte) (st tr : (BitVec 256) → (BitVec 256))
    (hc : toCode .staticcall (addr.toNat % 2 ^ 160) 0 = true)
    (hsz : (T.outs.getD (machineCalls w).length ByteArray.empty).size < 2 ^ 256) :
    callFlag (OS codes T) (w ++ [.call .staticcall [gas, addr] input st tr]) =
        (if T.oks.getD (machineCalls w).length false then 1 else 0) ∧
      ∀ rest, machineCalls rest = [] →
        RdRel (OS codes T) (w ++ [.call .staticcall [gas, addr] input st tr] ++ rest)
          (T.outs.getD (machineCalls w).length ByteArray.empty) := by
  have hm := machineCalls_static w gas addr input st tr
  refine ⟨?_, fun rest hrest => ?_⟩
  · show (if tabResult T.oks T.outs _ = 0 then _ else _) = _
    simp only [tabResult, hm, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      List.length_append, List.length_singleton, Nat.add_sub_cancel, tabResp, hc, ite_true]
    cases T.oks.getD (machineCalls w).length false <;> simp
  · have hmr : machineCalls (w ++ [.call .staticcall [gas, addr] input st tr] ++ rest) =
        machineCalls w ++ [(.staticcall, addr.toNat % 2 ^ 160, 0, input.map BitVec.toNat)] := by
      rw [machineCalls_append, hm, hrest, List.append_nil]
    refine ⟨?_, fun i hi => ?_⟩
    · show ((OS codes T).env "returndatasize" _ []).toNat = _
      rw [OS_env codes T _ _ _ (by decide) rfl]
      simp only [tabEnv, show ("returndatasize" = "extcodesize") = False by simp, ite_false, hmr,
        List.getLast?_append, List.getLast?_singleton, Option.some_or, List.length_append,
        List.length_singleton, Nat.add_sub_cancel, tabResp, hc, ite_true, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hsz
    · show ((OS codes T).env "returndata" _ [BitVec.ofNat 256 i]).setWidth 8 = _
      rw [OS_env codes T _ _ _ (by decide) rfl]
      simp only [tabEnv, show ("returndata" = "extcodesize") = False by simp, ite_false, hmr,
        List.getLast?_append, List.getLast?_singleton, Option.some_or, List.length_append,
        List.length_singleton, Nat.add_sub_cancel, tabResp, hc, ite_true]
      apply BitVec.eq_of_toNat_eq
      have hi' : i < 2 ^ 256 := by omega
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec,
        Nat.mod_eq_of_lt hi', EthLib.Base.byteAt, hi, dite_true]
      have := ((T.outs.getD (machineCalls w).length ByteArray.empty).get! i).toNat_lt
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [ByteArray.get!]
      clear this
      revert hi
      simp only [List.getD_eq_getElem?_getD]
      intro hi
      exact congrArg UInt8.toNat (data_getElem! _ i hi)

/-- The world of a table whose one static call succeeded with data `d` answers that call with
success and `d`: the open world of `OS_agree` admits successful calls. -/
example (d : ByteArray) (world : SolidCore.Solidity.Shared.OpenWorld)
    (request : EvmCompiler.Simulation.CallRequest)
    (hc : toCode (machineKind request.kind) (addressToWord request.codeAddress)
      (u256ToWord request.transferValue) = true) :
    ((tabWorld [true] [d] []).ans [] (.external world (.call request))).map
      (fun a => (a.success, a.returnData)) = some (true, d) := by
  rw [tabWorld_static _ _ _ _ _ _ hc]
  rfl

/-- info: 'SolidCore.Refinement.Solar.AssembleCallWorld.OS_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OS_agree

/-- info: 'SolidCore.Refinement.Solar.AssembleCallWorld.OS_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OS_ok

/-- info: 'SolidCore.Refinement.Solar.AssembleCallWorld.OS_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OS_static

end SolidCore.Refinement.Solar.AssembleCallWorld
