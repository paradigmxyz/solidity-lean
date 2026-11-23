import Verify.LoopSource.Equiv.CounterCtx

/-!
# Counter's created runtime and constructor state, tied to the expected theorem's

* \`runtime\`: the 248 bytes solar's init code for Counter returns (the freeze-head producer's), and
  \`code_eq\`: they are \`runtimeCode SolarTV.Export.Counter.bytecode\`, the bytes \`counter_expected\`
  is about.
* \`source_half\`: for the pinned \`[n]\`, \`n ∈ {5, 8}\`, SolidCore's constructor on the base contract at
  the expected theorem's fuel leaves \`[(1, n)]\` (\`DeployedAtWith\`, from \`CounterCtor.gates_of\`).
* \`same_d\`: that constructor state is the one the expected theorem's \`semAt\` runs against (every
  \`LoadDeployed\` on \`[n]\`, by \`loadDeployed_of\` and \`loadDeployed_unique\`).
-/

namespace Verify.LoopSource.Equiv.CounterSame
open SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic.Loop Contracts.VerifyCounter.Source
open SolidCore.Verify.Generic

def runtime : ByteArray := EthLib.Execution.Evm.Logic.NatCode.ofNat 358428864301163451273378810530872899898082717561197358686725586419607596196545658369331925709730609542679460203559819392543919900056812201079448262153444061678501347039648643997905486562160824253190538114523810118107911691080329021209325701955021240952145017981121210938615244181255552376491044004558096003002201893628609018393136739578158187593336400527665713548986383614536873557900546536157691149950657077262744717893586463341756649037861229527810560792277076586339092952507798157060288841097843398137586624444522896943189042086609226742146615737669522505030325179607568539028303001878035176701 248

theorem code_eq : runtimeCode SolarTV.Export.Counter.bytecode = runtime := by
  apply ByteArray.ext; decide +kernel

theorem source_half {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat} (hn : n = 5 ∨ n = 8) :
    ∃ d, Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs [n]) d [(1, n)] := by
  apply Verify.Lifecycle.deployedAtWith_of
  rcases hn with rfl | rfl
  · exact (Verify.LoopSource.Equiv.CounterCtor.gates_of hc).2.1
  · exact (Verify.LoopSource.Equiv.CounterCtor.gates_of hc).1

/-- **The lifecycle statement's constructor state is the expected theorem's.** -/
theorem same_d {c : TypeCheck.CheckedContract} {n : Nat} {d d' : Source.State}
    (hd : Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs [n]) d [(1, n)])
    (hd' : LoadDeployed fuel c [n] d') : d = d' :=
  Verify.LoopSource.Equiv.CounterLoad.loadDeployed_unique (loadDeployed_of hd).1 hd'

end Verify.LoopSource.Equiv.CounterSame

/-- info: 'Verify.LoopSource.Equiv.CounterSame.same_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterSame.same_d
