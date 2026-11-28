import Verify.Shapes
import SolidCore.Refinement.SourceOracle

/-!
# The shape of a certified compilation in an open world

`Shapes.Functional` runs the bytecode in EthLib's state with only the contract and its caller
(`Target.preState`), so every external call reaches an account without code. For a contract
whose functions call other contracts (a pair reading its tokens' balances and paying them), that
closed world makes every such function revert, and a specification of their successes holds
vacuously. This file states the same three obligations with the environment quantified, as
requirement E asks:

* `TargetEnv`: the other accounts of the target's state (address, code, storage, balance), any
  list the statement admits (`EnvOk`); `Target.runWithIn env gas code call` is
  `Final.Target.runWith` with those accounts added, observing the contract's own logs only.
* `OpenFunctional`: equivalence (every result of the exact bytecode in every admitted environment,
  at every gas below `2 ^ 256`, is SolidCore's result in some admitted open world `W`, or an
  inert failure, or a result that only a world outside the admitted ones explains: `Unadmitted`,
  reported as such), termination with an allowed status in **every** admitted world (never by choosing
  a terminating oracle), and the specification of every source result in every admitted world.
  The allowed statuses and the specification may read the world (a ghost step that depends on the
  answers of the calls).

`OpenFunctional.bytecode_any` is what it says of the bytes: every result in every admitted
environment is allowed and meets the specification for some admitted world, or changes nothing.
No resources obligation: a gas bound for code whose callees spend gas is not stated here.

The world the equivalence picks is existential per run: the statement does not say it is the one
the environment's code computes (causal consistency is the stage's business; the specification
holds in every admitted world, so the conclusion does not depend on which).
-/

namespace SolidCore.Refinement.Shapes

open SolarTV SolidCore.Refinement SolidCore.Refinement.Final
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.State

/-- One other account of the target's state. -/
structure EnvAccount where
  addr : Nat
  code : ByteArray
  storage : List (Nat × Nat)
  balance : Nat
  nonce : Nat

/-- The other accounts of the target's state. -/
abbrev TargetEnv := List EnvAccount

/-- The environment's accounts are distinct addresses below `2 ^ 160`, neither the contract nor
its caller. -/
def TargetEnv.WF (env : TargetEnv) : Prop :=
  (env.map (·.addr)).Nodup ∧ ∀ a ∈ env, a.addr < 2 ^ 160 ∧ a.addr ≠ selfAddress ∧ a.addr ≠ callerAddress

namespace Target

/-- `Target.preState` with the environment's accounts, storage and code added. -/
def preStateIn (env : TargetEnv) (code : ByteArray) (call : Call) : TransactionState :=
  let hash := EthLib.Cryptography.Hash.Keccak.keccak256 code
  let storage : Std.ExtTreeMap Bytes32 U256 :=
    call.storage.foldl (fun m kv => m.insert (Refinement.Target.storageKey kv.1) (BitVec.ofNat 256 kv.2)) ∅
  let accounts0 : Std.ExtTreeMap Address Account :=
    ((∅ : Std.ExtTreeMap Address Account).insert (Refinement.Target.address selfAddress)
        { nonce := 1, balance := 0, codeHash := hash }).insert (Refinement.Target.address callerAddress)
        { nonce := 0, balance := BitVec.ofNat 256 call.callvalue,
          codeHash := EthLib.Cryptography.Hash.Keccak.keccak256 .empty }
  let storage0 : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256) :=
    (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert
      (Refinement.Target.address selfAddress) storage
  let code0 : Std.ExtTreeMap Hash32 ByteArray := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert hash code
  let pre : State := env.foldl (fun (s : State) a =>
      let h := EthLib.Cryptography.Hash.Keccak.keccak256 a.code
      { accounts := s.accounts.insert (Refinement.Target.address a.addr)
          { nonce := a.nonce, balance := BitVec.ofNat 256 a.balance, codeHash := h },
        storage := s.storage.insert (Refinement.Target.address a.addr)
          (a.storage.foldl (fun m kv =>
            m.insert (Refinement.Target.storageKey kv.1) (BitVec.ofNat 256 kv.2)) ∅),
        code := s.code.insert h a.code })
    { accounts := accounts0, storage := storage0, code := code0 }
  TransactionState.ofBlock
    { preState := pre, accountWrites := ∅, storageWrites := ∅, codeWrites := ∅,
      storageClears := ∅ }

/-- `Final.Target.runWith` in the environment `env`: the contract's own logs, storage and
output. -/
def runWithIn (env : TargetEnv) (gas : Nat) (code : ByteArray) (call : Call) : Option Observable :=
  match processMessage (Meter := Nat) .fusaka (Final.Target.messageWith gas code call)
      (preStateIn env code call) Substate.empty with
  | .error _ => none
  | .ok ⟨evm, _⟩ =>
    let success := evm.error.isNone
    some
      { success
        output := evm.output.toList.map (·.toNat)
        logs :=
          if success then
            (evm.substate.logs.toList.filter fun log =>
                log.address == Refinement.Target.address selfAddress).map fun log =>
              (log.topics.map fun topic => bytesToNat topic.toList,
                log.data.toList.map (·.toNat))
          else []
        storage := fun slot =>
          if success then
            (evm.state.getStorage (Refinement.Target.address selfAddress)
              (Refinement.Target.storageKey slot)).toNat
          else slotValue call.storage slot }

end Target

/-- A result outside what the admitted worlds explain: some world of the wide class `Wide` gives it,
and no admitted world does (such as a run that only a world changing the contract's storage
during one of its external calls explains). -/
def Unadmitted (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract)
    (Wide Admit : World → Prop) (call : Call) (obs : Observable) : Prop :=
  (∃ W, Wide W ∧ Source.runIn W fuel c call = some obs) ∧
    ∀ W, Admit W → Source.runIn W fuel c call ≠ some obs

/-- **Equivalence, termination and the specification in an open world.** `Admit` are the worlds
the specification and termination speak of; a result of the bytes that only a world of the wider
class `Wide` explains is reported as `Unadmitted`, never as meeting the specification. -/
structure OpenFunctional (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract)
    (code : ByteArray) (EnvOk : TargetEnv → Prop) (Wide Admit : World → Prop) (Valid : Call → Prop)
    (Allowed Post : World → Call → Observable → Prop) : Prop where
  inhabited : ∃ call, Valid call
  equiv : ∀ env, EnvOk env → ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call → ∀ obs,
    Target.runWithIn env gas code call = some obs →
      (∃ W, Admit W ∧ Source.runIn W fuel c call = some obs) ∨ Inert call obs ∨
        Unadmitted fuel c Wide Admit call obs
  terminates : ∀ W, Admit W → ∀ call, Valid call →
    ∃ obs, Source.runIn W fuel c call = some obs ∧ Allowed W call obs
  meets : ∀ W, Admit W → ∀ call, Valid call → ∀ obs,
    Source.runIn W fuel c call = some obs → Post W call obs

/-- **What the bytecode does in every admitted environment**: every result, at any gas below
`2 ^ 256`, is allowed and meets the specification in some admitted world, or changes nothing, or
is explained by no admitted world. -/
theorem OpenFunctional.bytecode_any {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {code : ByteArray} {EnvOk : TargetEnv → Prop} {Wide Admit : World → Prop} {Valid : Call → Prop}
    {Allowed Post : World → Call → Observable → Prop}
    (h : OpenFunctional fuel c code EnvOk Wide Admit Valid Allowed Post) (env : TargetEnv)
    (he : EnvOk env) (gas : Nat) (hg : gas < 2 ^ 256) (call : Call) (hc : Valid call)
    (obs : Observable) (hrun : Target.runWithIn env gas code call = some obs) :
    (∃ W, Admit W ∧ Allowed W call obs ∧ Post W call obs) ∨ Inert call obs ∨
      Unadmitted fuel c Wide Admit call obs := by
  rcases h.equiv env he gas hg call hc obs hrun with ⟨W, hW, hs⟩ | e | e
  · obtain ⟨obs', hs', ha⟩ := h.terminates W hW call hc
    obtain rfl : obs' = obs := Option.some.inj (hs'.symm.trans hs)
    exact Or.inl ⟨W, hW, ha, h.meets W hW call hc obs' hs'⟩
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)

/-- The obligations compose from their parts: a source total in every admitted world, its
specification in every admitted world, and the per-run equivalence of the bytecode. -/
theorem OpenFunctional.of_parts {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {code : ByteArray} {EnvOk : TargetEnv → Prop} {Wide Admit : World → Prop} {Valid : Call → Prop}
    {Allowed Post : World → Call → Observable → Prop}
    (hin : ∃ call, Valid call)
    (heq : ∀ env, EnvOk env → ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call → ∀ obs,
      Target.runWithIn env gas code call = some obs →
        (∃ W, Admit W ∧ Source.runIn W fuel c call = some obs) ∨ Inert call obs ∨
          Unadmitted fuel c Wide Admit call obs)
    (hterm : ∀ W, Admit W → ∀ call, Valid call →
      ∃ obs, Source.runIn W fuel c call = some obs ∧ Allowed W call obs)
    (hspec : ∀ W, Admit W → Meets (solidCoreIn W fuel) c Valid (Post W)) :
    OpenFunctional fuel c code EnvOk Wide Admit Valid Allowed Post :=
  ⟨hin, heq, hterm, fun W hW => hspec W hW⟩

/-- info: 'SolidCore.Refinement.Shapes.OpenFunctional.bytecode_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OpenFunctional.bytecode_any

end SolidCore.Refinement.Shapes

