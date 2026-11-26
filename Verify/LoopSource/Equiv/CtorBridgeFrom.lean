import Verify.LoopSource.Equiv.CtorBridge
import Verify.LoopSource.Equiv.LoopFrom

/-!
# The load-level deployed run from any caller

\`deployed_run_entry_from a\`: \`deployed_run_entry\` with the call sent by \`a\`. From a load-level
deployment, a call of a function whose body runs to \`b\` from the symbolic-caller first state
(\`BodyRunsFrom\`) runs to the tree's observable at caller word \`a\`.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic

theorem deployed_run_entry_from (a : Nat) {fuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : LoadDeployed fuel c ws0 d) {σ : List (Nat × Nat)} {store : Nat → Nat}
    (hstore : ∀ k, ((σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage)[k % 2 ^ 256]?).getD 0 = store k)
    (hok : ∀ k, store (k % wordSize) % wordSize = store k)
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) {b : Br}
    (hb : BodyRunsFrom { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok (args.map .word)) :
    Refinement.Source.runFromArgs a fuel ws0 c
        { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (fixObs σ (T.eval ⟨args, store, solHash, a⟩).obs) :=
  deployed_run_entry_at a (e := .caller) hd hstore hok hsel hfind hw hret hb hT args rfl hlen hargs
    hclean hdec

end SolidCore.Refinement.Generic.Loop

/-- info: 'SolidCore.Refinement.Generic.Loop.deployed_run_entry_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Generic.Loop.deployed_run_entry_from
