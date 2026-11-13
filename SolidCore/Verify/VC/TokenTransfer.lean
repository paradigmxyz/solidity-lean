import SolidCore.Verify.VC.Token

/-!
# solar-verify's `Token.transfer`, bound to SolidCore

`transfer`'s three ensures clauses on distinct addresses (the sender's and the recipient's new
balances, and every other balance unchanged) as a `Triple` against SolidCore's `Source.run`, proved
from solar-verify's own obligations: `transfer_triple` takes the verdict `Valid Export.Token.script`,
and its proof reads each clause off the obligation `checkScript_sound` gives, at the assignment
`trEnv` that a call binds. Nothing in the proof re-derives a clause in Lean: the bridge is the
binding lemma `trStore_eval`, which says that SolidCore's storage after the call, read through
`balanceOf`'s layout (`balanceOf[k]` at slot `keccak(k, 0)`), is solar-verify's array term `S2` at
`trEnv`, for every address.

The binding is explicit:
* widths: `amount` is the call's second word, below `2 ^ 256`; `to` its first, which the erased tree
  reverts on above `2 ^ 160 - 1` (any word is in scope, dirty ones included);
* environment: `msg.sender` is the stage's caller `callerWord`, `msg.value` is 0 (the stage's scope);
* storage: `totalSupply` is slot 1, `balanceOf` is the array `k ↦ storage (keccak(k, 0))`;
* ghost: `sumBalances` is not program state, so the assignment sets it to `totalSupply`, which is
  what solar-verify's assumed invariant asks; the clauses proved here do not mention it;
* Keccak: `HashInj`, injectivity of the mapping slot on address keys, is a hypothesis of the
  theorem, never an axiom. It is what makes `to`, the sender and every third address name distinct
  slots.
-/

namespace SolidCore.Verify.VC.Token

open SolidCore.Verify SolidCore.Verify.VC SolidCore.Refinement SolidCore.Refinement.Abi
open SolidCore.Refinement.Generic

/-- `transfer` as the stage's ABI sees it: two words, any value below `2 ^ 256`. -/
def fnTransfer : Fn := ⟨transferSel, [.uint 256, .uint 256]⟩

/-- The erasure of `transfer`, as the generic source stage computes it. -/
def transferTree : Tree :=
  (Tree.ite
      (WExpr.bin
        (BinOp.gt)
        (WExpr.arg 0)
        (WExpr.lit 1461501637330902918203684832716283019655932542975))
      (Tree.halt false [] [] [])
      (Tree.ite
        (WExpr.un
          (UnOp.iszero)
          (WExpr.bin
            (BinOp.lt)
            (WExpr.sinit
              (WExpr.hash
                (WExpr.lit 8192)
                (WExpr.lit 0)))
            (WExpr.arg 1)))
        (Tree.ite
          (WExpr.bin
            (BinOp.lt)
            (WExpr.sinit
              (WExpr.hash
                (WExpr.lit 8192)
                (WExpr.lit 0)))
            (WExpr.arg 1))
          (Tree.halt
            false
            [OByte.lit 78,
             OByte.lit 72,
             OByte.lit 123,
             OByte.lit 113,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 0,
             OByte.lit 17]
            []
            [])
          (Tree.ite
            (WExpr.bin
              (BinOp.lt)
              (WExpr.bin
                (BinOp.add)
                (WExpr.sel
                  (WExpr.bin
                    (BinOp.eq)
                    (WExpr.hash
                      (WExpr.arg 0)
                      (WExpr.lit 0))
                    (WExpr.hash
                      (WExpr.lit 8192)
                      (WExpr.lit 0)))
                  (WExpr.bin
                    (BinOp.sub)
                    (WExpr.sinit
                      (WExpr.hash
                        (WExpr.lit 8192)
                        (WExpr.lit 0)))
                    (WExpr.arg 1))
                  (WExpr.sinit
                    (WExpr.hash
                      (WExpr.arg 0)
                      (WExpr.lit 0))))
                (WExpr.arg 1))
              (WExpr.sel
                (WExpr.bin
                  (BinOp.eq)
                  (WExpr.hash
                    (WExpr.arg 0)
                    (WExpr.lit 0))
                  (WExpr.hash
                    (WExpr.lit 8192)
                    (WExpr.lit 0)))
                (WExpr.bin
                  (BinOp.sub)
                  (WExpr.sinit
                    (WExpr.hash
                      (WExpr.lit 8192)
                      (WExpr.lit 0)))
                  (WExpr.arg 1))
                (WExpr.sinit
                  (WExpr.hash
                    (WExpr.arg 0)
                    (WExpr.lit 0)))))
            (Tree.halt
              false
              [OByte.lit 78,
               OByte.lit 72,
               OByte.lit 123,
               OByte.lit 113,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 0,
               OByte.lit 17]
              []
              [])
            (Tree.halt
              true
              [OByte.byteOf (WExpr.lit 1) 0,
               OByte.byteOf (WExpr.lit 1) 1,
               OByte.byteOf (WExpr.lit 1) 2,
               OByte.byteOf (WExpr.lit 1) 3,
               OByte.byteOf (WExpr.lit 1) 4,
               OByte.byteOf (WExpr.lit 1) 5,
               OByte.byteOf (WExpr.lit 1) 6,
               OByte.byteOf (WExpr.lit 1) 7,
               OByte.byteOf (WExpr.lit 1) 8,
               OByte.byteOf (WExpr.lit 1) 9,
               OByte.byteOf (WExpr.lit 1) 10,
               OByte.byteOf (WExpr.lit 1) 11,
               OByte.byteOf (WExpr.lit 1) 12,
               OByte.byteOf (WExpr.lit 1) 13,
               OByte.byteOf (WExpr.lit 1) 14,
               OByte.byteOf (WExpr.lit 1) 15,
               OByte.byteOf (WExpr.lit 1) 16,
               OByte.byteOf (WExpr.lit 1) 17,
               OByte.byteOf (WExpr.lit 1) 18,
               OByte.byteOf (WExpr.lit 1) 19,
               OByte.byteOf (WExpr.lit 1) 20,
               OByte.byteOf (WExpr.lit 1) 21,
               OByte.byteOf (WExpr.lit 1) 22,
               OByte.byteOf (WExpr.lit 1) 23,
               OByte.byteOf (WExpr.lit 1) 24,
               OByte.byteOf (WExpr.lit 1) 25,
               OByte.byteOf (WExpr.lit 1) 26,
               OByte.byteOf (WExpr.lit 1) 27,
               OByte.byteOf (WExpr.lit 1) 28,
               OByte.byteOf (WExpr.lit 1) 29,
               OByte.byteOf (WExpr.lit 1) 30,
               OByte.byteOf (WExpr.lit 1) 31]
              [(WExpr.hash
                  (WExpr.arg 0)
                  (WExpr.lit 0),
                WExpr.bin
                  (BinOp.add)
                  (WExpr.sel
                    (WExpr.bin
                      (BinOp.eq)
                      (WExpr.hash
                        (WExpr.arg 0)
                        (WExpr.lit 0))
                      (WExpr.hash
                        (WExpr.lit 8192)
                        (WExpr.lit 0)))
                    (WExpr.bin
                      (BinOp.sub)
                      (WExpr.sinit
                        (WExpr.hash
                          (WExpr.lit 8192)
                          (WExpr.lit 0)))
                      (WExpr.arg 1))
                    (WExpr.sinit
                      (WExpr.hash
                        (WExpr.arg 0)
                        (WExpr.lit 0))))
                  (WExpr.arg 1)),
               (WExpr.hash
                  (WExpr.lit 8192)
                  (WExpr.lit 0),
                WExpr.bin
                  (BinOp.sub)
                  (WExpr.sinit
                    (WExpr.hash
                      (WExpr.lit 8192)
                      (WExpr.lit 0)))
                  (WExpr.arg 1))]
              [])))
        (Tree.halt
          false
          [OByte.lit 8,
           OByte.lit 195,
           OByte.lit 121,
           OByte.lit 160,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 32,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 12,
           OByte.lit 105,
           OByte.lit 110,
           OByte.lit 115,
           OByte.lit 117,
           OByte.lit 102,
           OByte.lit 102,
           OByte.lit 105,
           OByte.lit 99,
           OByte.lit 105,
           OByte.lit 101,
           OByte.lit 110,
           OByte.lit 116,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0,
           OByte.lit 0]
          []
          [])))

/-- How SolidCore dispatches `transfer` and the generic source stage erases it. -/
def transferShape? : Option (Option (Nat × Option Tree)) :=
  match contract? with
  | .ok c => some ((c.core.findFunctionBySelector? transferSel).map fun f =>
      (f.params.length, eraseFn (envOf c.core) fuel f))
  | .error _ => none

kernel_rfl transferShape_eq transferShape? (some (some (2, some transferTree))) using selector_eq mkIdx_eq

/-! ## The Lean obligations -/

namespace Ob

def rcpt : Tm := .ivar "to"
def add (a b : Tm) : Tm := .app "+" [a, b]
def leA (t : Tm) : Tm := .app "<=" [t, .num (2 ^ 160 - 1)]
def sel (a i : Tm) : Tm := .app "select" [a, i]
def sto (a i v : Tm) : Tm := .app "store" [a, i, v]
def B : Tm := .avar "balanceOf"
/-- The balances after the sender's debit. -/
def S1 : Tm := sto B ms (sub bal amt)
/-- `balanceOf` after the call, as solar-verify encodes it. -/
def S2 : Tm := sto S1 rcpt (add (sel S1 rcpt) amt)

end Ob

open Ob in
/-- The facts every successful `transfer` meets at `trEnv`. -/
def trHyps : List Tm :=
  [eq ts sum, eq mv (.num 0), .app ">=" [bal, amt], le0 (sub bal amt), leW (sub bal amt),
    le0 (add (sel S1 rcpt) amt), leW (add (sel S1 rcpt) amt), arrFact "k" "balanceOf" (2 ^ 256 - 1),
    le0 amt, leW amt, le0 rcpt, leA rcpt, le0 ts, leW ts, le0 sum, leW sum, le0 mv, leW mv,
    .app "not" [eq ms (.num 0)], le0 ms, .app "<=" [ms, .num (2 ^ 160 - 1)]]

open Ob in
/-- The sender's clause: `msg.sender != to ==> balanceOf[msg.sender] == old(…) - amount`. -/
def trGoalFrom : Tm := .app "=>" [.app "not" [eq ms rcpt], eq (sel S2 ms) (sub bal amt)]

open Ob in
/-- The recipient's clause: `msg.sender != to ==> balanceOf[rcpt] == old(balanceOf[rcpt]) + amount`. -/
def trGoalTo : Tm := .app "=>" [.app "not" [eq ms rcpt], eq (sel S2 rcpt) (add (sel B rcpt) amt)]

open Ob in
/-- The frame: every other address keeps its balance. -/
def trGoalFrame : Tm :=
  .all "a" (.app "=>" [.app "and" [.app "and" [le0 (.ivar "a"), leA (.ivar "a")]],
    .app "=>" [.app "and" [.app "not" [eq (.ivar "a") ms], .app "not" [eq (.ivar "a") rcpt]],
      eq (sel S2 (.ivar "a")) (sel B (.ivar "a"))]])

/-- The Lean obligations of `transfer`'s clauses. -/
def trObs : List (List Tm × Tm) := [(trHyps, trGoalFrom), (trHyps, trGoalTo), (trHyps, trGoalFrame)]

/-- solar-verify's script for `Token` has obligations that `checkOb` normalizes to each of them. -/
theorem transfer_check : checkScript Export.Token.script trObs = true := by
  decide +kernel


/-! ## The binding -/

/-- Injectivity of `balanceOf`'s slot on address keys: distinct addresses name distinct slots. A
hypothesis on Keccak-256, stated where it is used, never assumed. -/
def HashInj : Prop := ∀ x y, x < 2 ^ 160 → y < 2 ^ 160 → solHash x 0 = solHash y 0 → x = y

/-- `balanceOf` as an array, through its storage layout. -/
def balArr (s : Storage) : Int → Int := fun k => s (solHash k.toNat 0)

/-- The assignment of solar-verify's names that a call of `transfer` binds: `to = t`, `amount = a`,
`msg.sender` the stage's caller, `totalSupply` slot 1, `balanceOf` its layout in the storage `s`,
the ghost `sumBalances` set to `totalSupply`, and every other name 0. -/
def trEnv (t a : Nat) (s : Storage) : Env :=
  ⟨fun x => if x = "amount" then a else if x = "to" then t else if x = "msg.sender" then callerWord
      else if x = "totalSupply" then s 1 else if x = "sumBalances" then s 1 else 0,
    fun _ => False,
    fun x => if x = "balanceOf" then balArr s else fun _ => 0⟩

/-- The recipient's balance after the debit: the sender's own when they are one address. -/
def midTo (t a : Nat) (s : Storage) : Nat := if t = callerWord then s senderSlot - a else s (solHash t 0)

theorem S2_eval (t a : Nat) (s : Storage) (j : Int) :
    (Ob.S2.eval (trEnv t a s)).toArr j =
      if j = t then (if t = callerWord then balArr s callerWord - a else balArr s t) + a
      else if j = callerWord then balArr s callerWord - a else balArr s j := by
  simp [Ob.S2, Ob.S1, Ob.sto, Ob.sel, Ob.add, Ob.B, Ob.rcpt, Ob.sub, Ob.bal, Ob.amt, Ob.ms,
    Tm.eval, Tm.evalList, applyOp, Value.toArr, Value.toInt, trEnv, callerWord]
  by_cases h1 : j = t <;> by_cases h2 : t = 8192 <;> by_cases h3 : j = 8192 <;>
    simp [h1, h2, h3] <;> omega

theorem hashT (t : Nat) : solHash t 0 % 2 ^ 256 = solHash t 0 := Nat.mod_eq_of_lt (solHash_lt t 0)

/-- What a successful run of QtransferQ's erased tree shows: QtoQ is an address, the sender had
the amount, the recipient's credit does not overflow, and the storage changes in exactly the
recipient's and the sender's slots. QHashInjQ decides the tree's test of whether they are one. -/
theorem tr_success (inj : HashInj) (s : Storage) (hs : ∀ k, s k < 2 ^ 256) (t a : Nat)
    (ht : t < 2 ^ 256) (ha : a < 2 ^ 256) :
    let R := transferTree.eval (valOf [t, a] s)
    R.success = true → t < 2 ^ 160 ∧ a ≤ s senderSlot ∧ midTo t a s + a < 2 ^ 256 ∧
      ∀ n < 2 ^ 256, R.store n = if n = solHash t 0 then midTo t a s + a
        else if n = senderSlot then s senderSlot - a else s n := by
  intro R hR
  have hsm : ∀ k, s k % 2 ^ 256 = s k := fun k => Nat.mod_eq_of_lt (hs k)
  have ham : a % 2 ^ 256 = a := Nat.mod_eq_of_lt ha
  have htm : t % 2 ^ 256 = t := Nat.mod_eq_of_lt ht
  have hss : senderSlot % 2 ^ 256 = senderSlot := by decide
  have h8 : 8192 % 2 ^ 256 = 8192 := by decide
  have h0 : 0 % 2 ^ 256 = 0 := by decide
  have hA : 1461501637330902918203684832716283019655932542975 % 2 ^ 256 =
      1461501637330902918203684832716283019655932542975 := by decide
  have h1 := hs senderSlot
  have hmid : midTo t a s = if t = 8192 then s senderSlot - a else s (solHash t 0) := rfl
  simp only [R, transferTree, Tree.eval] at hR ⊢
  simp only [WExpr.eval, BinOp.eval, UnOp.eval, valOf, Generic.wordSize, List.getD_cons_zero,
    List.getD_cons_succ, htm, hA, h8, h0, ham, hss, hsm, hashT, hash_eq] at hR ⊢
  split_ifs at hR ⊢ <;> simp only at hR
  · rename_i hgt hlt _ hc hov
    have hta : t < 2 ^ 160 := by omega
    have ht8 : t = 8192 := inj t 8192 hta (by decide) (hc.trans hash_eq.symm)
    subst ht8
    have hsub : (s senderSlot + (2 ^ 256 - a)) % 2 ^ 256 = s senderSlot - a := by omega
    rw [hsub, Nat.mod_eq_of_lt (by omega : s senderSlot - a < 2 ^ 256)] at hov
    have hm : midTo 8192 a s = s senderSlot - a := by simp [hmid]
    refine ⟨hta, by omega, by omega, ?_⟩
    intro n hn
    rw [hm, hc]
    simp only [Writes.store, WExpr.eval, BinOp.eval, Generic.wordSize, List.getD_cons_zero,
      List.getD_cons_succ, h8, h0, ham, hss, hsm, hashT, hash_eq, Nat.mod_eq_of_lt hn, hsub]
    by_cases hn' : n = senderSlot
    · subst hn'; simp; omega
    · simp [hn', Ne.symm hn']
  · rename_i hgt hlt _ hc hov
    have hta : t < 2 ^ 160 := by omega
    have ht8 : t ≠ 8192 := fun h => hc (h ▸ hash_eq)
    have hm : midTo t a s = s (solHash t 0) := by simp [hmid, ht8]
    have hst := hs (solHash t 0)
    have hno : s (solHash t 0) + a < 2 ^ 256 := by omega
    refine ⟨hta, by omega, by omega, ?_⟩
    intro n hn
    rw [hm]
    simp only [Writes.store, WExpr.eval, BinOp.eval, Generic.wordSize, List.getD_cons_zero,
      List.getD_cons_succ, htm, h8, h0, ham, hss, hsm, hashT, hash_eq, Nat.mod_eq_of_lt hn]
    by_cases hn1 : n = solHash t 0
    · subst hn1; simp [hc]; omega
    · by_cases hn2 : n = senderSlot
      · subst hn2; simp [hc, Ne.symm hc]; omega
      · simp [hn1, hn2, Ne.symm hn1, Ne.symm hn2]

theorem balArr_nat (s : Storage) (x : Nat) : balArr s x = s (solHash x 0) := by simp [balArr]

theorem balArr_caller (s : Storage) : balArr s callerWord = s senderSlot := by
  rw [balArr_nat]; exact congrArg (fun n => ((s n : Nat) : Int)) hash_eq


section
variable (t a : Nat) (s : Storage)
@[simp] theorem trEnv_amount : (trEnv t a s).i "amount" = a := rfl
@[simp] theorem trEnv_to : (trEnv t a s).i "to" = t := rfl
@[simp] theorem trEnv_sender : (trEnv t a s).i "msg.sender" = 8192 := rfl
@[simp] theorem trEnv_bal : (trEnv t a s).a "balanceOf" = balArr s := rfl
end

section
variable (t a : Nat) (s : Storage) (n : Int)
@[simp] theorem trEnvA_a : ((trEnv t a s).setI "a" n).i "a" = n := rfl
@[simp] theorem trEnvA_to : ((trEnv t a s).setI "a" n).i "to" = t := rfl
@[simp] theorem trEnvA_sender : ((trEnv t a s).setI "a" n).i "msg.sender" = 8192 := rfl
@[simp] theorem trEnvA_amount : ((trEnv t a s).setI "a" n).i "amount" = a := rfl
@[simp] theorem trEnvA_bal : ((trEnv t a s).setI "a" n).a "balanceOf" = balArr s := rfl

/-- solar-verify's array term does not read the frame's bound address. -/
theorem S2_setI : Ob.S2.eval ((trEnv t a s).setI "a" n) = Ob.S2.eval (trEnv t a s) := by
  apply Tm.eval_congr
  intro y hy
  have hna : y ≠ "a" := by
    rintro rfl
    revert hy
    decide
  exact ⟨by simp [Env.setI, hna], rfl, rfl⟩
end

/-- The binding: after a successful `transfer`, every address's `balanceOf` slot in SolidCore's
storage holds solar-verify's array term `S2` at `trEnv`. -/
theorem trStore_eval (inj : HashInj) (s : Storage) (hs : ∀ k, s k < 2 ^ 256) (t a : Nat)
    (ht : t < 2 ^ 256) (ha : a < 2 ^ 256)
    (hR : (transferTree.eval (valOf [t, a] s)).success = true) (x : Nat) (hx : x < 2 ^ 160) :
    (((transferTree.eval (valOf [t, a] s)).store (solHash x 0) : Nat) : Int) =
      (Ob.S2.eval (trEnv t a s)).toArr x := by
  obtain ⟨hta, hle, hov, hst⟩ := tr_success inj s hs t a ht ha hR
  rw [hst _ (solHash_lt x 0), S2_eval]
  have hc : (callerWord : Int) = 8192 := rfl
  have hxt : (solHash x 0 = solHash t 0) ↔ x = t :=
    ⟨inj x t hx hta, fun h => h ▸ rfl⟩
  have hx8 : (solHash x 0 = senderSlot) ↔ x = 8192 :=
    ⟨fun h => inj x 8192 hx (by decide) (h.trans hash_eq.symm), fun h => h ▸ hash_eq⟩
  have hmid : midTo t a s = if t = 8192 then s senderSlot - a else s (solHash t 0) := rfl
  rw [balArr_caller, balArr_nat, balArr_nat]
  by_cases h1 : x = t
  · subst h1
    by_cases h2 : x = 8192
    · subst h2; simp [hmid]; omega
    · simp [hmid, h2, hc]; omega
  · by_cases h2 : x = 8192
    · subst h2
      have : ¬ (8192 : Int) = t := by omega
      simp [hxt, h1, hash_eq, this]; omega
    · have h1' : ¬ (x : Int) = t := by omega
      have h2' : ¬ (x : Int) = 8192 := by omega
      simp [hxt, h1, hx8, h2, h1', h2', hc]

theorem trHyps_hold (s : Storage) (hs : ∀ k, s k < 2 ^ 256) (t a : Nat) (hta : t < 2 ^ 160)
    (ha : a < 2 ^ 256) (hle : a ≤ s senderSlot) (hov : midTo t a s + a < 2 ^ 256) :
    ∀ x ∈ trHyps, x.Holds (trEnv t a s) := by
  have hc : (callerWord : Int) = 8192 := rfl
  have h8 : balArr s 8192 = s senderSlot := balArr_caller s
  have hmid : midTo t a s = if t = 8192 then s senderSlot - a else s (solHash t 0) := rfl
  have h1 := hs senderSlot
  have h1' := hs (solHash t 0)
  have h2 := hs 1
  simp only [trHyps, List.mem_cons, List.mem_nil_iff, or_false]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl) <;>
  simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toProp, Value.toInt, Value.toArr, Value.eq,
    trEnv, Ob.amt, Ob.ms, Ob.ts, Ob.sum, Ob.mv, Ob.bal, Ob.le0, Ob.leW, Ob.sub, Ob.eq, Ob.add,
    Ob.leA, Ob.sel, Ob.sto, Ob.S1, Ob.B, Ob.rcpt, arrFact, Env.setI, hc, h8, balArr_nat] <;>
  first
  | omega
  | (intro n; have := hs (solHash n.toNat 0); simp only [balArr]; omega)
  | (by_cases ht8 : t = 8192 <;> simp [ht8, hmid] at hov ⊢ <;> omega)

/-- `transfer`'s ensures clauses on distinct addresses, as SolidCore sees them: on success, for
the call's words `t = to` and `a = amount`, the sender's slot drops by `a` and the recipient's
rises by `a` when they differ, and every other address's slot is unchanged. -/
def trPost (call : Call) (obs : SolarTV.Observable) : Prop :=
  obs.success = true →
    let t := (argWords 2 call).getD 0 0
    let a := (argWords 2 call).getD 1 0
    let s := initStorage call
    (t ≠ callerWord → obs.storage (solHash callerWord 0) = s (solHash callerWord 0) - a) ∧
    (t ≠ callerWord → obs.storage (solHash t 0) = s (solHash t 0) + a) ∧
    (∀ x < 2 ^ 160, x ≠ callerWord → x ≠ t → obs.storage (solHash x 0) = s (solHash x 0))

/-- The goal of one of `transfer`'s obligations, at `trEnv`, from solar-verify's verdict. -/
theorem tr_obligation (hv : Valid Export.Token.script) {φ : Tm} (hφ : (trHyps, φ) ∈ trObs)
    {s : Storage} (hs : ∀ k, s k < 2 ^ 256) {t a : Nat} (hta : t < 2 ^ 160) (ha : a < 2 ^ 256)
    (hle : a ≤ s senderSlot) (hov : midTo t a s + a < 2 ^ 256) : φ.Holds (trEnv t a s) :=
  checkScript_sound transfer_check hv _ hφ _ (trHyps_hold s hs t a hta ha hle hov)

/-- `Token.transfer` meets its three ensures clauses on distinct addresses on the stage's scope,
given solar-verify's verdict on its script for `Token` and injectivity of the mapping slot on
address keys. Each clause is read off solar-verify's obligation for it (`tr_obligation`) through
the binding `trStore_eval`. -/
theorem transfer_triple (hv : Valid Export.Token.script) (inj : HashInj)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Triple fuel c (stageScope fnTransfer [(2, 4096)]) (fun _ => True) trPost := by
  have hdep := burnShape_eq
  simp only [burnShape?, hc, Option.some.injEq, Prod.mk.injEq] at hdep
  obtain ⟨d, hd⟩ := Wide.deployedAt_of hdep.1
  have hshape := transferShape_eq
  simp only [transferShape?, hc, Option.some.injEq, Option.map_eq_some_iff, Prod.mk.injEq] at hshape
  obtain ⟨f, hf, hlen, hT⟩ := hshape
  have himpl := implements_tree (fn := fnTransfer) hd (by decide) hf hlen hT rfl
  apply triple_of_wp himpl
  rintro _ ⟨σ, hcov, fn', hfn', args, hl, hargs, rfl⟩ -
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  obtain ⟨t, a, rfl⟩ : ∃ t a, args = [t, a] := by
    match args, hl with
    | [t, a], _ => exact ⟨t, a, rfl⟩
  have ht : t < 2 ^ 256 := hargs t (by simp)
  have ha : a < 2 ^ 256 := hargs a (by simp)
  have hw : argWords 2 ({ calldata := Abi.calldata fnTransfer.sel [t, a], callvalue := 0, storage := σ } : Call) =
      [t, a] := argWords_calldata _ [t, a] hargs 0 σ
  rw [vc_eq, treeModel_run, show fnTransfer.params.length = 2 from rfl, hw]
  set s := initStorage ({ calldata := Abi.calldata fnTransfer.sel [t, a], callvalue := 0, storage := σ } : Call)
    with hs_def
  have hs : ∀ k, s k < 2 ^ 256 := fun k => Generic.slotValue_lt σ k
  unfold resOutcome
  split
  · next hok =>
    intro _
    obtain ⟨hta, hle, hov, -⟩ := tr_success inj s hs t a ht ha hok
    have hb := trStore_eval inj s hs t a ht ha hok
    have hcw : (callerWord : Int) = 8192 := rfl
    have h8 : balArr s 8192 = (s senderSlot : Int) := balArr_caller s
    have hob := fun φ (hφ : (trHyps, φ) ∈ trObs) => tr_obligation hv hφ hs hta ha hle hov
    have gFrom := hob trGoalFrom (by simp [trObs])
    have gTo := hob trGoalTo (by simp [trObs])
    have gFrame := hob trGoalFrame (by simp [trObs])
    simp only [trGoalFrom, trGoalTo, trGoalFrame, Tm.Holds, Tm.eval, Tm.evalList, applyOp,
      Value.toProp, Value.toInt, Value.toArr, Value.eq, Ob.eq, Ob.sel, Ob.sub, Ob.add, Ob.le0,
      Ob.leA, Ob.bal, Ob.B, Ob.ms, Ob.amt, Ob.rcpt, S2_setI] at gFrom gTo gFrame
    simp only [observe, hw, List.getD_cons_zero, List.getD_cons_succ]
    rw [← hs_def]
    have hsl : solHash callerWord 0 = senderSlot := hash_eq
    refine ⟨fun hne => ?_, fun hne => ?_, fun x hx hx8 hxt => ?_⟩
    · have e : (((transferTree.eval (valOf [t, a] s)).store senderSlot : Nat) : Int) =
          (Ob.S2.eval (trEnv t a s)).toArr 8192 := by
        have := hb callerWord (by decide); rwa [hsl] at this
      have g := gFrom (by simp; omega)
      simp [h8] at g
      simp only [Value.toArr] at e g
      rw [hsl]
      omega
    · have e := hb t hta
      have g := gTo (by simp; omega)
      simp [balArr_nat] at g
      simp only [Value.toArr] at e g
      omega
    · have e := hb x hx
      have hx8' : ¬ (x : Int) = 8192 := by intro h; apply hx8; exact_mod_cast h
      have hxt' : ¬ (x : Int) = t := by omega
      have hxA : (x : Int) ≤ 1461501637330902918203684832716283019655932542975 := by omega
      have g := gFrame x
      simp [balArr_nat, hx8', hxt', hxA, S2_setI] at g
      simp only [Value.toArr] at e g
      omega
  · intro h; simp_all [observe]

/-- info: 'SolidCore.Verify.VC.Token.transfer_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transfer_triple

end SolidCore.Verify.VC.Token
