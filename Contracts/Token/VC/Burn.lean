import Verify.VC
import Contracts.Token.VC.Source
import Contracts.Token.VC.Export
import SolidCore.Refinement.KernelRfl
import Verify.VC.KernelIdx

/-!
# solar-verify's `Token.burn` against SolidCore

The kernel's evaluation fixes what SolidCore does with `scripts/verify/Token.sol`: it type checks,
its constructor leaves only `owner` (slot 2) and no logs, `burn(uint256)` dispatches to a function
of one parameter, and the generic source stage erases it to `burnTree` (`burnShape_eq`). As in the
Token source stage, the checker's selectors come from a table each of whose entries the kernel
checks against Keccak-256 once.
-/

namespace SolidCore.Verify.VC.Token

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic
open SolidCore.Solidity SolidCore.Solidity.Source

/-- The interpreter fuel of SolidCore's runs. -/
def fuel : Nat := 4096

/-- SolidCore's checked `Token`. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract SolidCore.Verify.VC.Source.Token.importedSourceUnit "Token"

/-- The selector of `balanceOf(address)`. -/
abbrev balanceofSel : Nat := 1889567281

/-- The selector of `balanceOf(address)`, by Keccak-256 of its signature. -/
def selBalanceOf : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "balanceOf(address)"

kernel_rfl selBalanceOf_eq selBalanceOf balanceofSel

/-- The selector of `totalSupply()`. -/
abbrev totalsupplySel : Nat := 404098525

/-- The selector of `totalSupply()`, by Keccak-256 of its signature. -/
def selTotalSupply : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "totalSupply()"

kernel_rfl selTotalSupply_eq selTotalSupply totalsupplySel

/-- The selector of `owner()`. -/
abbrev ownerSel : Nat := 2376452955

/-- The selector of `owner()`, by Keccak-256 of its signature. -/
def selOwner : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "owner()"

kernel_rfl selOwner_eq selOwner ownerSel

/-- The selector of `mint(address,uint256)`. -/
abbrev mintSel : Nat := 1086394137

/-- The selector of `mint(address,uint256)`, by Keccak-256 of its signature. -/
def selMint : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "mint(address,uint256)"

kernel_rfl selMint_eq selMint mintSel

/-- The selector of `transfer(address,uint256)`. -/
abbrev transferSel : Nat := 2835717307

/-- The selector of `transfer(address,uint256)`, by Keccak-256 of its signature. -/
def selTransfer : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "transfer(address,uint256)"

kernel_rfl selTransfer_eq selTransfer transferSel

/-- The selector of `burn(uint256)`. -/
abbrev burnSel : Nat := 1117154408

/-- The selector of `burn(uint256)`, by Keccak-256 of its signature. -/
def selBurn : SolidCore.Solidity.Shared.Word :=
  SolidCore.Solidity.Source.ABI.selectorFromSignature "burn(uint256)"

kernel_rfl selBurn_eq selBurn burnSel

/-- `ABI.selectorFromSignature`, with `Token`'s selectors by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "balanceOf(address)" then balanceofSel
  else if s = "totalSupply()" then totalsupplySel
  else if s = "owner()" then ownerSel
  else if s = "mint(address,uint256)" then mintSel
  else if s = "transfer(address,uint256)" then transferSel
  else if s = "burn(uint256)" then burnSel
  else SolidCore.Solidity.Source.ABI.selectorFromSignature s

theorem selector_eq : SolidCore.Solidity.Source.ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  split_ifs <;> subst_vars
  exacts [selBalanceOf_eq, selTotalSupply_eq, selOwner_eq, selMint_eq, selTransfer_eq, selBurn_eq, rfl]

/-- The revert data of `Panic(0x11)`, byte by byte. -/
def panic11 : List OByte :=
  [78, 72, 123, 113].map .lit ++ (List.replicate 31 (OByte.lit 0)) ++ [.lit 17]

/-- The erasure of `burn`, as the generic source stage computes it. -/
def burnTree : Tree :=
  (.ite (.bin .lt (.sinit (.hash (.lit 8192) (.lit 0))) (.arg 0)) (.halt false panic11 [] [])
    (.ite (.bin .lt (.sel (.bin .eq (.lit 1) (.hash (.lit 8192) (.lit 0)))
        (.bin .sub (.sinit (.hash (.lit 8192) (.lit 0))) (.arg 0)) (.init 1)) (.arg 0))
      (.halt false panic11 [] [])
      (.halt true [] [(.lit 1, .bin .sub (.sel (.bin .eq (.lit 1) (.hash (.lit 8192) (.lit 0)))
          (.bin .sub (.sinit (.hash (.lit 8192) (.lit 0))) (.arg 0)) (.init 1)) (.arg 0)),
        (.hash (.lit 8192) (.lit 0), .bin .sub (.sinit (.hash (.lit 8192) (.lit 0))) (.arg 0))] [])))

/-- Whether `Token` deploys with `owner` alone in storage and no logs, and how SolidCore dispatches
`burn` and the generic source stage erases it. -/
def burnShape? : Option (Bool × Option (Nat × Option Tree)) :=
  match contract? with
  | .ok c => some (Wide.deployedAt fuel c [(2, 4096)],
      (c.core.findFunctionBySelector? burnSel).map fun f => (f.params.length, eraseFn (envOf c.core) fuel f))
  | .error _ => none

kernel_rfl burnShape_eq burnShape? (some (true, some (1, some burnTree))) using selector_eq mkIdx_eq

open SolidCore.Verify SolidCore.Verify.VC SolidCore.Refinement SolidCore.Refinement.Abi
open SolidCore.Refinement.Generic

/-- `burn` as the stage's ABI sees it. -/
def fnBurn : Fn := ⟨burnSel, [.uint 256]⟩

/-- The slot of `balanceOf[msg.sender]` for the stage's caller `callerWord`. -/
def senderSlot : Nat :=
  55339514551095541597166361489097532198990872027936225909895186517043906691032

/-- `balanceOf[msg.sender]`'s slot, by Keccak-256. -/
def senderSlotOf : Nat := solHash callerWord 0

kernel_rfl senderSlot_eq senderSlotOf senderSlot

theorem hash_eq : solHash 8192 0 = senderSlot := senderSlot_eq

theorem tree_success (s : Nat → Nat) (hs : ∀ k, s k < 2 ^ 256) (a : Nat) (ha : a < 2 ^ 256) :
    let R := burnTree.eval (valOf [a] s)
    R.success = true → a ≤ s senderSlot ∧ a ≤ s 1 ∧
      R.store senderSlot = s senderSlot - a ∧ R.store 1 = s 1 - a := by
  intro R
  have hsm : ∀ k, s k % 2 ^ 256 = s k := fun k => Nat.mod_eq_of_lt (hs k)
  have ham : a % 2 ^ 256 = a := Nat.mod_eq_of_lt ha
  have hss : senderSlot % 2 ^ 256 = senderSlot := by decide
  have hne : (1 = senderSlot) = False := by decide
  have hne' : (senderSlot = 1) = False := by decide
  have h1 := hs senderSlot
  have h2 := hs 1
  have h8 : 8192 % 2 ^ 256 = 8192 := by decide
  have h0 : 0 % 2 ^ 256 = 0 := by decide
  have h1' : 1 % 2 ^ 256 = 1 := by decide
  simp only [R, burnTree, Tree.eval, WExpr.eval, BinOp.eval, valOf, Generic.wordSize,
    h8, h0, h1', hash_eq, List.getD_cons_zero, hss, hsm, ham, hne, ite_false, ite_true]
  split_ifs <;> simp only [Writes.store, WExpr.eval, BinOp.eval, Generic.wordSize, hash_eq, hss, hsm,
    ham, hne, hne', h8, h0, h1', ite_false, ite_true, List.getD_cons_zero, 
    false_implies, true_implies] <;> first | contradiction | omega

/-! ## solar-verify's obligation for `burn`, on the Lean side -/

namespace Ob

def amt : Tm := .ivar "amount"
def ms : Tm := .ivar "msg.sender"
def ts : Tm := .ivar "totalSupply"
def sum : Tm := .ivar "sumBalances"
def mv : Tm := .ivar "msg.value"
def bal : Tm := .app "select" [.avar "balanceOf", ms]
def le0 (t : Tm) : Tm := .app "<=" [.num 0, t]
def leW (t : Tm) : Tm := .app "<=" [t, .num (2 ^ 256 - 1)]
def sub (a b : Tm) : Tm := .app "-" [a, b]
def eq (a b : Tm) : Tm := .app "=" [a, b]

end Ob

open Ob in
/-- The facts the Lean side of `burn`'s ensures clause rests on: the invariant, no value, the
success path's two range checks, and the words' ranges. -/
def burnHyps : List Tm :=
  [eq ts sum, eq mv (.num 0), le0 (sub bal amt), leW (sub bal amt), le0 (sub ts amt),
    leW (sub ts amt), le0 bal, leW bal, le0 amt, leW amt, le0 ts, leW ts, le0 sum, leW sum, le0 mv,
    leW mv, .app "not" [eq ms (.num 0)], le0 ms, .app "<=" [ms, .num (2 ^ 160 - 1)]]

open Ob in
/-- solar-verify's encoding of `balanceOf[msg.sender]` after `burn`. -/
def burnStore : Tm := .app "select" [.app "store" [.avar "balanceOf", ms, sub bal amt], ms]

open Ob in
/-- `burn`'s ensures clause `balanceOf[msg.sender] == old(balanceOf[msg.sender]) - amount` as
solar-verify states it, of its own encoding of the function's effect. -/
def burnGoal : Tm := eq burnStore (sub bal amt)

/-- solar-verify's script for `Token` has an obligation that `checkOb` normalizes to
`burnHyps → burnGoal`. -/
theorem burn_check : checkScript Export.Token.script [(burnHyps, burnGoal)] = true := by
  decide +kernel

/-- The assignment of solar-verify's names that a call of `burn` on `amount` gives, from the
balance `b` of the caller and the total supply `t`; the ghost `sumBalances` is chosen equal to
`totalSupply`, which the invariant assumes. -/
def burnEnv (a b t : Nat) : Env where
  i := fun x => if x = "amount" then a else if x = "msg.sender" then callerWord
      else if x = "totalSupply" then t else if x = "sumBalances" then t else 0
  b := fun _ => False
  a := fun x => if x = "balanceOf" then fun k => if k = callerWord then b else 0 else fun _ => 0

theorem burnHyps_hold {a b t : Nat} (ha : a ≤ b) (ht : a ≤ t) (hb : b < 2 ^ 256) (htt : t < 2 ^ 256) :
    ∀ x ∈ burnHyps, x.Holds (burnEnv a b t) := by
  have hca : callerWord = 8192 := rfl
  simp only [burnHyps, List.mem_cons, List.mem_nil_iff, or_false]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl) <;>
  simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.select, Value.store, Value.toProp, Value.toInt, Value.toArr, Value.eq,
    burnEnv, Ob.amt, Ob.ms, Ob.ts, Ob.sum, Ob.mv, Ob.bal, Ob.le0, Ob.leW, Ob.sub, Ob.eq, hca] <;>
  omega

/-- What solar-verify's encoding of the caller's new balance is at `burnEnv`: the old balance less
the amount. -/
theorem burnStore_eval (a b t : Nat) :
    (burnStore.eval (burnEnv a b t)).toInt = (b : Int) - a := by
  have hca : callerWord = 8192 := rfl
  simp [burnStore, Tm.eval, Tm.evalList, applyOp, Value.select, Value.store, Value.toInt, Value.toArr, burnEnv, Ob.amt, Ob.ms,
    Ob.bal, Ob.sub, hca]

/-- `burn`'s postcondition: on success, the caller's balance and the total supply drop by the
amount. -/
def burnPost (call : Call) (obs : SolarTV.Observable) : Prop :=
  obs.success = true →
    obs.storage senderSlot = initStorage call senderSlot - (argWords 1 call).getD 0 0 ∧
      obs.storage 1 = initStorage call 1 - (argWords 1 call).getD 0 0

/-- solar-verify's verdict on its script for `Token` gives `burn`'s ensures obligation at the
assignment of every successful call: `checkScript_sound`, with the facts discharged from the
success path. -/
theorem burn_obligation (hv : Valid Export.Token.script) {a b t : Nat} (ha : a ≤ b) (ht : a ≤ t)
    (hb : b < 2 ^ 256) (htt : t < 2 ^ 256) : burnGoal.Holds (burnEnv a b t) :=
  checkScript_sound burn_check hv (burnHyps, burnGoal) (List.mem_singleton_self _) _
    (burnHyps_hold ha ht hb htt)

/-- `burnPost` of a call's argument words and storage. -/
def burnP (args : List Nat) (s : Storage) (o : SolarTV.Observable) : Prop :=
  o.success = true →
    o.storage senderSlot = s senderSlot - args.getD 0 0 ∧ o.storage 1 = s 1 - args.getD 0 0

/-- The binding of `burn`'s erased tree: its success path lowers the caller's slot and slot 1 by
the amount. It needs no obligation: solar-verify's goal for this clause selects the stored value
back out of its own `store` (`burnStore_eval`), which is valid in the array theory;
`burn_obligation` is the transfer through `checkScript_sound` that a goal not valid on its own
(the invariant, `transfer`'s frame) needs. -/
theorem burn_binds :
    Binds fnBurn burnTree [] (fun args s => burnEnv (args.getD 0 0) (s senderSlot) (s 1)) burnP := by
  rintro args s hl hargs hs - hok
  obtain ⟨a, rfl⟩ : ∃ a, args = [a] := by
    match args, hl with
    | [a], _ => exact ⟨a, rfl⟩
  obtain ⟨-, -, h1, h2⟩ := tree_success s hs a (hargs a (List.mem_singleton_self a)) hok
  exact ⟨h1, h2⟩

/-- What `burnShape_eq` says, as the generic theorems take it: `Token` deploys with `owner` alone
in storage and no logs, and the source stage erases `burn` to `burnTree`. -/
theorem burn_erased {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    ∃ d f, Wide.DeployedAt fuel c d [(2, 4096)] ∧ c.core.findFunctionBySelector? fnBurn.sel = some f ∧
      f.params.length = fnBurn.params.length ∧ eraseFn (envOf c.core) fuel f = some burnTree := by
  have h := burnShape_eq
  simp only [burnShape?, hc, Option.some.injEq, Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨hdep, f, hf, hlen, hT⟩ := h
  obtain ⟨d, hd⟩ := Wide.deployedAt_of hdep
  exact ⟨d, f, hd, hf, hlen, hT⟩

/-- `burn` meets its ensures clause on the stage's scope: the generic `triple_of_binds` with the
binding `burn_binds` and no obligation. -/
theorem burn_triple {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : contract? = .ok c) :
    Triple fuel c (stageScope fnBurn [(2, 4096)]) (fun _ => True) burnPost := by
  obtain ⟨d, f, hd, hf, hlen, hT⟩ := burn_erased hc
  exact triple_of_binds hd (by decide) hf hlen hT (fun _ h => by simp at h) burn_binds

/-- info: 'SolidCore.Verify.VC.Token.burn_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms burn_triple

/-- info: 'SolidCore.Verify.VC.Token.burn_obligation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms burn_obligation

end SolidCore.Verify.VC.Token
