import Verify.LoopSource.MirLink.Statement
import Verify.LoopSource.MirLink.Link
import Verify.LoopSource.Proof.LoopVC
import Verify.LoopSource.Generic.Interface

/-!
# The link checked against the Statement's expected type

The kernel checks that the link's proof has exactly the type `StatementLink` stated in
`Statement.lean`, a module that imports no proof. It also checks that the loop route's theorem
`body_runs_vc` (the ranking-certificate proof checked from solar-verify's obligations) gives the
Statement's source half, and that none of these depends on the hand-written `SourceBump.body_runs`
or on the theorems built on it (`Source.runs`, `Source.terminates`, `Source.success_spec`): the
source half comes from the loop route alone. The axioms are the standard three.
-/

open Lean Elab Command in
/-- `#assert_not_uses thm c`: whether the constant `c` occurs in the transitive closure of the
constants `thm`'s type and value use. Both names must exist, so a misspelled name cannot pass. -/
elab "#assert_not_uses " t:ident ppSpace c:ident : command => do
  let env ← getEnv
  let target := c.getId
  unless env.contains target do throwError "unknown constant {target}"
  unless env.contains t.getId do throwError "unknown constant {t.getId}"
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[t.getId]
  let mut found := false
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if n == target then
      found := true
      break
    if let some ci := env.find? n then
      for m in ci.type.getUsedConstants do
        unless seen.contains m do todo := todo.push m
      if let some v := ci.value? (allowOpaque := true) then
        for m in v.getUsedConstants do
          unless seen.contains m do todo := todo.push m
  logInfo m!"uses {target}: {found}"

namespace Verify.LoopSource.MirLink
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop Contracts.VerifyCounter.Source

example : StatementLink := statement_link

example : Generic.GenericLink := Generic.generic_link

/-- Counter's loop as a record of the exported interface. -/
def counterRecord (ρ : Val) : Interface.LoopRecord :=
  { H := headerS, P := Contracts.VerifyCounter.LoopBinding.P ρ, m := Contracts.VerifyCounter.LoopBinding.m,
    c := Contracts.VerifyCounter.LoopBinding.c, bb := Contracts.VerifyCounter.LoopBinding.bb }

/-- The loop route's obligations are the record's `Obl`. -/
example (ev : List EventDecl) (tbl : FunctionTable) (ρ : Val) (ctx : Context) (hok : ρ.Ok)
    (hpre : ρ.store 0 + nOf ρ ≤ ρ.store 1) :
    (counterRecord ρ).Obl 3 (env ev tbl) ctx cond post body (Contracts.VerifyCounter.Source.Q ρ (env ev tbl) ctx) :=
  Contracts.VerifyCounter.LoopVC.obl_vc ev tbl ρ ctx hok hpre

/-- **Counter.bump's Statement source half, from the loop route's theorem.** -/
theorem counter_statement_source_half : StatementSourceHalf :=
  source_half_of_headline Contracts.VerifyCounter.LoopVC.body_runs_vc

/-- **The whole Statement from the loop route's theorem**, given the bytecode's two obligations. -/
theorem counter_statement_of_loop (code : ByteArray) (Allowed Post : Call → Observable → Prop)
    (G : Call → Nat) (hA : OnTree Allowed) (hP : OnTree Post)
    (heq : ∀ c, Contracts.VerifyCounter.Source.contract? = .ok c →
      Shapes.Equiv stmtSem c code Contracts.VerifyCounter.Source.BumpCall)
    (hres : ∀ c, Contracts.VerifyCounter.Source.contract? = .ok c →
      Shapes.Resources stmtSem c code Contracts.VerifyCounter.Source.BumpCall G) :
    ∃ c, Contracts.VerifyCounter.Source.contract? = .ok c ∧
      Shapes.Certified stmtSem c code Contracts.VerifyCounter.Source.BumpCall Allowed Post G :=
  statement_link Contracts.VerifyCounter.LoopVC.body_runs_vc code Allowed Post G hA hP heq hres

end Verify.LoopSource.MirLink

/-- info: 'Verify.LoopSource.MirLink.statement_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.MirLink.statement_link

/-- info: 'Verify.LoopSource.MirLink.counter_statement_source_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.MirLink.counter_statement_source_half

/-- info: 'Verify.LoopSource.MirLink.counter_statement_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.MirLink.counter_statement_of_loop

/-- info: uses Contracts.VerifyCounter.Source.body_runs: false -/
#guard_msgs in
#assert_not_uses Verify.LoopSource.MirLink.counter_statement_source_half Contracts.VerifyCounter.Source.body_runs

/-- info: uses Contracts.VerifyCounter.Source.runs: false -/
#guard_msgs in
#assert_not_uses Verify.LoopSource.MirLink.counter_statement_source_half Contracts.VerifyCounter.Source.runs

/-- info: uses Contracts.VerifyCounter.Source.success_spec: false -/
#guard_msgs in
#assert_not_uses Verify.LoopSource.MirLink.counter_statement_source_half Contracts.VerifyCounter.Source.success_spec

/-- info: uses Contracts.VerifyCounter.Source.body_runs: false -/
#guard_msgs in
#assert_not_uses Verify.LoopSource.MirLink.counter_statement_of_loop Contracts.VerifyCounter.Source.body_runs

/-- info: uses Contracts.VerifyCounter.LoopVC.body_runs_vc: true -/
#guard_msgs in
#assert_not_uses Verify.LoopSource.MirLink.counter_statement_source_half Contracts.VerifyCounter.LoopVC.body_runs_vc

/-- info: uses Contracts.VerifyCounter.Source.bumpFn: false -/
#guard_msgs in
#assert_not_uses Verify.LoopSource.Generic.generic_link Contracts.VerifyCounter.Source.bumpFn

/-- info: uses Contracts.VerifyCounter.Source.contract?: false -/
#guard_msgs in
#assert_not_uses Verify.LoopSource.Generic.generic_link Contracts.VerifyCounter.Source.contract?

/-- info: uses Verify.LoopSource.RC.Headline.CounterBumpLoopHeadline: false -/
#guard_msgs in
#assert_not_uses Verify.LoopSource.Generic.generic_link Verify.LoopSource.RC.Headline.CounterBumpLoopHeadline

/-- info: uses Verify.LoopSource.Generic.generic_link: true -/
#guard_msgs in
#assert_not_uses Verify.LoopSource.MirLink.statement_link Verify.LoopSource.Generic.generic_link
