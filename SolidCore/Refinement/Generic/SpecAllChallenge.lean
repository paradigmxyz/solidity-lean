import SolidCore.Refinement.Generic.CtorAll
import SolidCore.Refinement.Generic.StageFromValue

/-!
# Challenge: constructor arguments for every word, and value sent to non-payable functions

The exact statements, each with `sorry`: a statement file only. Nothing imports it and no proof
uses it. The matching audit checks each proved declaration against its statement here with
`example : <statement> := <declaration>`.
-/

namespace SolidCore.Refinement.Generic.Challenge

open SolidCore.Refinement.Generic

theorem decode_uint256_word : ∀ (f : SolidCore.Solidity.Source.FunctionDef) (ws : List Nat), f.params.map SolidCore.Solidity.Source.BindingDecl.ty = ws.map (fun _ => SolidCore.Solidity.Source.Ty.uint256) → (∀ k ∈ f.paramAbiCleanups, k = .none ∨ k = .uint 256) → (f.paramAbiCleanups = [] ∨ f.paramAbiCleanups.length = ws.length) → (∀ w ∈ ws, w < 2 ^ 256) → SolidCore.Solidity.Source.ABI.decodeFunctionArgs? f (argData ws) = .ok (Verify.Lifecycle.wordArgs ws) := sorry

theorem CtorAdmits_of_fn : ∀ {c : SolidCore.Solidity.TypeCheck.CheckedContract} {f : SolidCore.Solidity.Source.FunctionDef} {initcode : ByteArray} {ws : List Nat}, SolidCore.Solidity.TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl = some f → f.payable = false → f.params.map SolidCore.Solidity.Source.BindingDecl.ty = ws.map (fun _ => SolidCore.Solidity.Source.Ty.uint256) → (∀ k ∈ f.paramAbiCleanups, k = .none ∨ k = .uint 256) → (f.paramAbiCleanups = [] ∨ f.paramAbiCleanups.length = ws.length) → (∀ w ∈ ws, w < 2 ^ 256) → CtorAdmits c initcode (Verify.Lifecycle.initArgs initcode ws) ws := sorry

theorem Source_run_of_load : ∀ {ws : List Nat} {src : SolidCore.Verify.Generic.Source ws} {c : SolidCore.Solidity.TypeCheck.CheckedContract} {initcode code creation : ByteArray} {s : List (Nat × Nat)} {d : SolidCore.Solidity.Source.State}, src.checked = .ok c → src.CreatedBy c initcode creation → SolidCore.Refinement.Deploys (Verify.Lifecycle.initArgs initcode ws) code s → DeployedAtLoad src.fuel c ws s d → SolidCore.Refinement.Deploys creation code s ∧ (∀ k, k < 2 ^ 256 → d.loadSlot k = slotOf s k) ∧ ∀ ctx : SolidCore.Verify.Generic.Context, ∀ call : SolidCore.Refinement.Call, (src.semAt ctx).run c call = (SolidCore.Solidity.TypeCheck.CheckedContract.callCalldataAtFromWithContext? src.fuel c { c.core.context with sender := SolidCore.Refinement.callerAddress, self := SolidCore.Refinement.selfAddress, value := call.callvalue } { d with storage := call.storage.foldl (fun acc kv => SolidCore.Solidity.Source.StorageMap.insertLoop acc kv.1 kv.2) d.storage } SolidCore.Refinement.selfAddress ctx.caller call.callvalue (call.calldata.data.toList.map (·.toNat))).map (SolidCore.Refinement.Source.observe call) := sorry

theorem resultFromArgs_value_rejected : ∀ {caller fuel : Nat} {ws : List Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract} {call : SolidCore.Refinement.Call} {d : SolidCore.Solidity.Source.State} {vs : List SolidCore.Solidity.Source.Value} {sel : Nat} {f : SolidCore.Solidity.Source.FunctionDef} {args : List SolidCore.Solidity.Source.Value}, SolidCore.Refinement.Source.deployArgs? fuel ws c = some (SolidCore.Solidity.Source.CallResult.returned d vs) → SolidCore.Solidity.Source.ABI.readSelector? (callBytes call) = some sel → c.core.findFunctionBySelector? sel = some f → SolidCore.Solidity.Source.ABI.decodeFunctionArgs? f ((callBytes call).drop SolidCore.Solidity.Source.ABI.selectorBytes) = .ok args → f.payable = false → SolidCore.Solidity.Shared.norm call.callvalue ≠ 0 → SolidCore.Refinement.Source.resultFromArgs? caller fuel ws c call = some { success := false, output := [], state := overlay d call } := sorry

theorem runFromArgs_value_inert : ∀ {caller fuel : Nat} {ws : List Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract} {call : SolidCore.Refinement.Call} {sel : Nat} {f : SolidCore.Solidity.Source.FunctionDef}, SolidCore.Solidity.Source.ABI.readSelector? (callBytes call) = some sel → c.core.findFunctionBySelector? sel = some f → f.payable = false → SolidCore.Solidity.Shared.norm call.callvalue ≠ 0 → ∀ {obs : SolidCore.Refinement.Observable}, SolidCore.Refinement.Source.runFromArgs caller fuel ws c call = some obs → obs.success = false ∧ obs.logs = [] ∧ obs.storage = SolidCore.Refinement.slotValue call.storage := sorry

end SolidCore.Refinement.Generic.Challenge
