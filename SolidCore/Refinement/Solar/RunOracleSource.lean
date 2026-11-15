import SolidCore.Refinement.Solar.RunOracle
import SolidCore.Refinement.SourceOracleSat

/-!
# The assembly premise of the composition under a call oracle

`Verify/SourceOracle.holds_of_runs` composes a specification proved of SolidCore in every open world
with the stages for every oracle and an assembly premise run by run: for every gas and call, an
oracle `o` and an open world `W` that agree (`CallsAgree o W`) under which the EVM IR gives the
bytecode's result or a failure that changes nothing. For a program the checker of code with loops
accepts, `assembly_of_checkL` gives that premise: the reads the certificate asks of the oracle
(`CertOk`: the caller, the hash, the block and the transaction) touch none of what `CallsAgree`
constrains (call results, storage after calls, return data, code sizes), so the failing world's
oracle with EthLib's caller, hash and environment meets both.
-/

namespace SolidCore.Refinement.Solar.RunOracle

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble

/-- EthLib's caller, hash and environment reads leave every other read of the oracle. -/
theorem env_envEth (o : Oracle) (n : String) (w : List Event) (a : List Word)
    (h : envRead n = none) : (envOracle (ethOracle o)).env n w a = o.env n w a := by
  simp [envOracle, ethOracle, h]

theorem codesAgree_envEth (o : Oracle) (w : List Event) (code : Nat → List SolidCore.Solidity.Byte) :
    CodesAgree (envOracle (ethOracle o)) w code ↔ CodesAgree o w code := by
  unfold CodesAgree
  simp only [env_envEth o "extcodesize" _ _ rfl]

theorem returndataSize_envEth (o : Oracle) (w : List Event) :
    returndataSize (envOracle (ethOracle o)) w = returndataSize o w :=
  env_envEth o "returndatasize" w [] rfl

theorem returndataByte_envEth (o : Oracle) (w : List Event) (j : Nat) :
    returndataByte (envOracle (ethOracle o)) w j = returndataByte o w j := by
  unfold returndataByte
  rw [env_envEth o "returndata" w _ rfl]

/-- EthLib's caller, hash and environment reads keep the oracle hypothesis of the open world. -/
theorem callsAgree_envEth {o : Oracle} {W : World} (h : CallsAgree o W) :
    CallsAgree (envOracle (ethOracle o)) W := by
  refine ⟨fun w hw => (codesAgree_envEth o _ _).2 (h.codes w hw), ?_, h.static⟩
  intro hh world req a ha w k s i st tr hl hm hst hcod
  obtain ⟨h1, h2, h3⟩ := h.calls hh world req a ha w k s i st tr hl hm hst
    ((codesAgree_envEth o _ _).1 hcod)
  refine ⟨h1, h2, fun rest hr => ?_⟩
  obtain ⟨r1, r2, r3⟩ := h3 rest hr
  exact ⟨by rw [returndataSize_envEth]; exact r1,
    fun j hj hj' => by rw [returndataByte_envEth]; exact r2 j hj hj', (codesAgree_envEth o _ _).2 r3⟩

/-- `envOracle` keeps EthLib's caller and hash. -/
theorem envOracle_oracleOk {o : Oracle} : OracleOk (envOracle (ethOracle o)) := ethOracle_ok o

/-- An oracle and an open world that agree, under which the certificate's reads are EthLib's. -/
theorem certOk_callsAgree (c : Cert) :
    ∃ (o : Oracle) (W : World), W.Open ∧ CallsAgree o W ∧ CertOk c o :=
  ⟨envOracle (ethOracle Witness.failOracle), Witness.failWorld, Witness.failWorld_open,
    callsAgree_envEth Witness.failAgree,
    fun _ => envOracle_oracleOk, fun _ => envOracle_ok _⟩

/-- **The assembly premise of `holds_of_runs`** for every program the checker of code with loops
accepts. -/
theorem assembly_of_checkL {p : Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : AssembleLoop.checkL p code c mx = true) (scope : Call → Prop) :
    ∀ gas call, scope call → ∃ (o : Oracle) (W : World), W.Open ∧ CallsAgree o W ∧
      Within (evmirSem o) (ethLibWith gas) p code (· = call) := by
  intro gas call _
  obtain ⟨o, W, hW, hagree, hok⟩ := certOk_callsAgree c
  exact ⟨o, W, hW, hagree, AssembleLoop.within_of_checkL hc o hok.1 _ gas hok.2⟩

/-- info: 'SolidCore.Refinement.Solar.RunOracle.assembly_of_checkL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assembly_of_checkL

end SolidCore.Refinement.Solar.RunOracle
