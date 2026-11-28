import SolidCore.Refinement.Generic.CtorAll
import SolidCore.Refinement.Generic.StageFromValue

/-!
# Audit: constructor arguments for every word, and value sent to non-payable functions

Each proved declaration has its challenge's exact statement (`example`), and `#print axioms`
shows its axioms: at most `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace SolidCore.Refinement.Generic.Audit

open SolidCore.Refinement.Generic

example : ∀ (f : SolidCore.Solidity.Source.FunctionDef) (ws : List Nat), f.params.map SolidCore.Solidity.Source.BindingDecl.ty = ws.map (fun _ => SolidCore.Solidity.Source.Ty.uint256) → (∀ k ∈ f.paramAbiCleanups, k = .none ∨ k = .uint 256) → (f.paramAbiCleanups = [] ∨ f.paramAbiCleanups.length = ws.length) → (∀ w ∈ ws, w < 2 ^ 256) → SolidCore.Solidity.Source.ABI.decodeFunctionArgs? f (argData ws) = .ok (Verify.Lifecycle.wordArgs ws) := @decode_uint256_word

example : ∀ {c : SolidCore.Solidity.TypeCheck.CheckedContract} {f : SolidCore.Solidity.Source.FunctionDef} {initcode : ByteArray} {ws : List Nat}, SolidCore.Solidity.TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl = some f → f.payable = false → f.params.map SolidCore.Solidity.Source.BindingDecl.ty = ws.map (fun _ => SolidCore.Solidity.Source.Ty.uint256) → (∀ k ∈ f.paramAbiCleanups, k = .none ∨ k = .uint 256) → (f.paramAbiCleanups = [] ∨ f.paramAbiCleanups.length = ws.length) → (∀ w ∈ ws, w < 2 ^ 256) → CtorAdmits c initcode (Verify.Lifecycle.initArgs initcode ws) ws := @CtorAdmits.of_fn

example : ∀ {ws : List Nat} {src : SolidCore.Verify.Generic.Source ws} {c : SolidCore.Solidity.TypeCheck.CheckedContract} {initcode code creation : ByteArray} {s : List (Nat × Nat)} {d : SolidCore.Solidity.Source.State}, src.checked = .ok c → src.CreatedBy c initcode creation → SolidCore.Refinement.Deploys (Verify.Lifecycle.initArgs initcode ws) code s → DeployedAtLoad src.fuel c ws s d → SolidCore.Refinement.Deploys creation code s ∧ (∀ k, k < 2 ^ 256 → d.loadSlot k = slotOf s k) ∧ ∀ ctx : SolidCore.Verify.Generic.Context, ∀ call : SolidCore.Refinement.Call, (src.semAt ctx).run c call = (SolidCore.Solidity.TypeCheck.CheckedContract.callCalldataAtFromWithContext? src.fuel c { c.core.context with sender := SolidCore.Refinement.callerAddress, self := SolidCore.Refinement.selfAddress, value := call.callvalue } { d with storage := call.storage.foldl (fun acc kv => SolidCore.Solidity.Source.StorageMap.insertLoop acc kv.1 kv.2) d.storage } SolidCore.Refinement.selfAddress ctx.caller call.callvalue (call.calldata.data.toList.map (·.toNat))).map (SolidCore.Refinement.Source.observe call) := @Source.run_of_load

example : ∀ {caller fuel : Nat} {ws : List Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract} {call : SolidCore.Refinement.Call} {d : SolidCore.Solidity.Source.State} {vs : List SolidCore.Solidity.Source.Value} {sel : Nat} {f : SolidCore.Solidity.Source.FunctionDef} {args : List SolidCore.Solidity.Source.Value}, SolidCore.Refinement.Source.deployArgs? fuel ws c = some (SolidCore.Solidity.Source.CallResult.returned d vs) → SolidCore.Solidity.Source.ABI.readSelector? (callBytes call) = some sel → c.core.findFunctionBySelector? sel = some f → SolidCore.Solidity.Source.ABI.decodeFunctionArgs? f ((callBytes call).drop SolidCore.Solidity.Source.ABI.selectorBytes) = .ok args → f.payable = false → SolidCore.Solidity.Shared.norm call.callvalue ≠ 0 → SolidCore.Refinement.Source.resultFromArgs? caller fuel ws c call = some { success := false, output := [], state := overlay d call } := @resultFromArgs?_value_rejected

example : ∀ {caller fuel : Nat} {ws : List Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract} {call : SolidCore.Refinement.Call} {sel : Nat} {f : SolidCore.Solidity.Source.FunctionDef}, SolidCore.Solidity.Source.ABI.readSelector? (callBytes call) = some sel → c.core.findFunctionBySelector? sel = some f → f.payable = false → SolidCore.Solidity.Shared.norm call.callvalue ≠ 0 → ∀ {obs : SolidCore.Refinement.Observable}, SolidCore.Refinement.Source.runFromArgs caller fuel ws c call = some obs → obs.success = false ∧ obs.logs = [] ∧ obs.storage = SolidCore.Refinement.slotValue call.storage := @runFromArgs_value_inert

end SolidCore.Refinement.Generic.Audit

#print axioms SolidCore.Refinement.Generic.decode_uint256_word
#print axioms SolidCore.Refinement.Generic.CtorAdmits.of_fn
#print axioms SolidCore.Refinement.Generic.Source.run_of_load
#print axioms SolidCore.Refinement.Generic.resultFromArgs?_value_rejected
#print axioms SolidCore.Refinement.Generic.runFromArgs_value_inert
