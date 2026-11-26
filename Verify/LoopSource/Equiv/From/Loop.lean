import Contracts.VerifyCounter.SourceLoop

/-!
# bump's loop in SolidCore from any caller: a ranking certificate

`bump(n)` of solar-verify's `Counter` (crates/verify/examples/Counter.sol),

    require(count + n <= limit, "over");
    for (uint256 i = 0; i < n; i++) { count++; }

as SolidCore's type checker leaves it (`bumpBody`, from `Contracts/VerifyCounter/SourceAst.lean`).
The loop's certificate (`cert`) is solar-verify's inferred invariant and measure for this loop,
`i <= n`, `count == old(count) + i` and `n - i`, stated of SolidCore's runtime at the header
(`Inv`, `rank`): the runtime is related (`StmtRel`) to the header state `headerS` whose words for
`n`, `i` and `count` are fresh (arguments 0, 1 and 2 of `hval ρ i (count0 + i)`). Each iteration is
run by SolidCore's interpreter (`eval_incField`, `eval_incVar`): the overflow guards of `count++`
and `i++` are false under the invariant and the `require`, the invariant comes back with `i + 1`,
and the rank falls by one; on exit `i = n` and `count` is `old(count) + n` (`exitS`).

These are `Contracts/VerifyCounter/SourceLoop.lean`'s states with `msg.sender` erased to the
symbolic caller (`caller := .caller`) instead of the default word, and the certificate is that
file's `certAt .caller`.
-/

namespace Verify.LoopSource.Equiv.From
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop

/-- The loop's condition, `i < n`. -/
def cond : Expr := .binary .lt (.castOp .uintCleanup 256 (.var "i")) (.castOp .uintCleanup 256 (.var "n"))

/-- The loop's update, `i++`. -/
def post : Stmt := .exprStmt (.incDec .add true (some (.uint 256)) (.var "i"))

/-- The loop's body, `count++`. -/
def body : Stmt :=
  .block [.exprStmt (.incDec .add true (some (.uint 256)) (.storageRead .header "count" []))]

/-- The header state: `n` is argument 0, `i` argument 1 and `count` (slot 0) argument 2. -/
def headerS : SymState :=
  { scopes := [[], [("i", .arg 1)], [], [], [("n", .arg 0)]], writes := [(.lit 0, .arg 2)], logs := [], caller := .caller }

/-- The state at the loop's exit, over the call's words: `i = n`, `count = old(count) + n`. -/
def exitS : SymState :=
  { scopes := [[], [("i", .arg 0)], [], [], [("n", .arg 0)]],
    writes := [(.lit 0, .bin .add (.init 0) (.arg 0))], logs := [], caller := .caller }

/-- The words of the header: the call's `n`, and `i` and `count`. -/
def hval (ρ : Val) (i c : Nat) : Val := ⟨[ρ.args.getD 0 0, i, c], ρ.store, ρ.hash, ρ.caller⟩

/-- The call's `n`. -/
def nOf (ρ : Val) : Nat := (WExpr.arg 0).eval ρ

/-- **The invariant** (inferred: `i <= n`, `count == old(count) + i`). -/
def Inv (ρ : Val) (E : EraseEnv) (ctx : Context) (rt : Runtime) : Prop :=
  ∃ i, i ≤ nOf ρ ∧ StmtRel (hval ρ i (ρ.store 0 + i)) E ctx rt headerS

/-- **The rank** (inferred: `n - i`), read off the runtime's `i`. -/
def rank (ρ : Val) (rt : Runtime) : Nat :=
  match rt.lookupLocal? "i" with
  | some (.word v) => nOf ρ - v
  | _ => 0

/-- What the loop ends in: normally, in the exit state. -/
def Q (ρ : Val) (E : EraseEnv) (ctx : Context) (r : Result) : Prop :=
  ∃ rt, r = .normal rt ∧ StmtRel ρ E ctx rt exitS

/-- The storage fields of `Counter`, as the type checker leaves them. -/
def countOk (E : EraseEnv) : Prop := fieldOf? E.fields "count" = some (0, 0, 32)

theorem nOf_lt (ρ : Val) : nOf ρ < wordSize := WExpr.eval_lt ρ _

theorem rank_of {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {i c : Nat}
    (h : StmtRel (hval ρ i c) E ctx rt headerS) (hi : i < wordSize) : rank ρ rt = nOf ρ - i :=
  Contracts.VerifyCounter.Source.rank_ofAt (w := .caller) h hi

/-- **bump's loop has a ranking certificate**, checked against SolidCore's interpreter: the
inferred measure `n - i` falls by one on every iteration. -/
theorem cert (ρ : Val) (E : EraseEnv) (ctx : Context) (hcount : countOk E)
    (hfacts : E.facts = []) (hpre : ρ.store 0 + nOf ρ ≤ ρ.store 1) :
    ForCert 3 E.tbl ctx cond post body (Inv ρ E ctx) (rank ρ) (Q ρ E ctx) :=
  Contracts.VerifyCounter.Source.certAt .caller ρ E ctx (fun _ _ => rfl) hcount hfacts hpre (rank ρ)
    fun i _ _ (hin : i < nOf ρ) h h' => by
      have hn := nOf_lt ρ
      rw [rank_of h' (by omega), rank_of h (by omega)]
      omega

/-- info: 'Verify.LoopSource.Equiv.From.cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cert

end Verify.LoopSource.Equiv.From
