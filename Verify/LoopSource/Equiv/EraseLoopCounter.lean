import Verify.LoopSource.Proof.EraseLoop

/-!
# Counter's `bump` loop, erased by `eraseLoopStmt`

A test instance of the counted-loop erasure on solar-verify's `Counter.bump(n)`
(crates/verify/examples/Counter.sol), whose body the type checker leaves as

    { n = n; { require(count + n <= limit, "over"); { uint256 i = 0; for (; i < n; i++) { count++; } } } }

The body, the storage fields and the function are restated here (`bumpBody`, `fields`, `bumpFn`,
the same values as `Contracts.VerifyCounter.Source.bumpBody`, `vcFields` and `bumpFn`, which
`EraseLoopCounterShape.lean` checks); nothing here imports a hand-written summary or ranking
certificate of the loop.

* `bump_erased`: the erasure computes, by `rfl`, to `bumpLoopBr`: `Panic(0x11)` when
  `count + n` wraps, `Error("over")` when it exceeds `limit`, and otherwise the loop's closed form,
  `n` iterations (`iters`: `n - 0` when `0 < n`, else `0`), with slot 0 holding `count + iters`;
  its two overflow guards (`count + iters` and `0 + iters` wrapping) are false whenever the
  `require` passed.
* `bump_runs`: `BodyRuns` of it at fuel `2 ^ 256 + 8`, by `bodyRuns_of_eraseLoop`.
* Controls: a loop without the update, a body that adds two, a `while` loop and too little fuel
  erase to `none`; the erasure is not a tree with a wrong exit value.
-/

namespace Verify.LoopSource.Equiv.EraseLoopCounter
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop

/-- A `uint256` storage field filling its slot. -/
def wordField (name : String) (slot : Nat) : StorageField :=
  { name := name, slot := slot, ty? := some Ty.uint256, layout? := some (StorageLayout.scalar Ty.uint256),
    transient := false, packedOffset := 0, packedBytes := 32, packedSigned := false }

/-- `Counter`'s storage fields. -/
def fields : List StorageField := [wordField "count" 0, wordField "limit" 1]

def s1 : Stmt := .assign (.var "n") (.castOp .uintCleanup 256 (.var "n"))

def s2 : Stmt :=
  .requireStmt
    (.binary .le
      (.castOp .uintCleanup 256 (.castOp .uintCleanup 256
        (.binary .add (.castOp .uintCleanup 256 (.storageRead .ref "count" []))
          (.castOp .uintCleanup 256 (.var "n")))))
      (.castOp .uintCleanup 256 (.storageRead .ref "limit" [])))
    (some "over")

def s3 : Stmt := .varDecl .uint256 "i" (some (.word 0))

/-- `i < n`. -/
def cnd : Expr := .binary .lt (.castOp .uintCleanup 256 (.var "i")) (.castOp .uintCleanup 256 (.var "n"))

/-- `i++`. -/
def post : Stmt := .exprStmt (.incDec .add true (some (.uint 256)) (.var "i"))

/-- `{ count++; }`. -/
def body : Stmt :=
  .block [.exprStmt (.incDec .add true (some (.uint 256)) (.storageRead .header "count" []))]

/-- `bump`'s body. -/
def bumpBody : Stmt := .block [s1, .block [s2, .block [s3, .forLoop .skip cnd post body]]]

/-- `bump`, as the type checker leaves it. -/
def bumpFn : FunctionDef :=
  { name := "bump", selector? := some 2987308228, payable := false,
    params := [{ name := "n", ty := Ty.uint256, isStorageRef := false }],
    paramAbiCleanups := [AbiCleanup.uint 256], returns := [], body := bumpBody, dispatchId? := none }

/-- The erasure environment of `bump`'s body (`bump`'s argument checks are empty: `n` is a
`uint256`). -/
def env (ev : List EventDecl) (tbl : FunctionTable) : EraseEnv :=
  { fields := fields, events := ev, tbl := tbl, facts := [] }

/-- The number of iterations: `n - 0` when `0 < n`, else `0`. -/
def iters : WExpr := .sel (.bin .lt (.lit 0) (.arg 0)) (.bin .sub (.arg 0) (.lit 0)) (.lit 0)

/-- `count + n` wraps. -/
def ovf : WExpr := .bin .lt (.bin .add (.init 0) (.arg 0)) (.init 0)

/-- `count + n <= limit`. -/
def le : WExpr := .un .iszero (.bin .gt (.bin .add (.init 0) (.arg 0)) (.init 1))

/-- The state at the end of the body: slot 0 holds `count + iters`. -/
def SF : SymState :=
  { scopes := [[("n", .arg 0)]], writes := [(.lit 0, .bin .add (.init 0) iters)], logs := [] }

/-- **bump's tree, with the loop's closed form.** -/
def bumpLoopBr : Br :=
  guards [ovf] (.ite le
    (guards [.bin .lt (.bin .add (.init 0) iters) (.init 0), .bin .lt (.bin .add (.lit 0) iters) (.lit 0)]
      (.leaf (.normal SF)))
    (.leaf (.reverted (.error "over"))))

/-- **The erasure computes** (the kernel evaluates it, `2 ^ 256 + 8` included). -/
theorem bump_erased (ev : List EventDecl) (tbl : FunctionTable) :
    eraseLoopStmt (env ev tbl) (2 ^ 256 + 8) bumpFn.body (initState bumpFn) = some bumpLoopBr := rfl

/-- **bump's body runs to `bumpLoopBr`**, from the erasure alone. -/
theorem bump_runs (ev : List EventDecl) (tbl : FunctionTable) :
    BodyRuns (env ev tbl) (2 ^ 256 + 8) bumpFn bumpLoopBr :=
  bodyRuns_of_eraseLoop (bump_erased ev tbl)

/-- The same, in the environment `loop_stage` takes, for a checked contract with `Counter`'s fields. -/
theorem bump_runs_checked (c : SolidCore.Solidity.TypeCheck.CheckedContract)
    (hfields : c.core.storageFields = fields) :
    BodyRuns { envOf c.core with facts := argFacts [2 ^ 256 - 1] 0 } (2 ^ 256 + 8) bumpFn bumpLoopBr := by
  have hE : ({ envOf c.core with facts := argFacts [2 ^ 256 - 1] 0 } : EraseEnv) =
      env c.core.eventDecls c.core.table := by
    simp only [envOf, env, hfields]
    rfl
  rw [hE]
  exact bump_runs _ _

/-! ## Controls -/

/-- A wrong exit: slot 0 one higher. -/
def wrongBr : Br :=
  guards [ovf] (.ite le
    (guards [.bin .lt (.bin .add (.init 0) iters) (.init 0), .bin .lt (.bin .add (.lit 0) iters) (.lit 0)]
      (.leaf (.normal { SF with writes := [(.lit 0, .bin .add (.bin .add (.init 0) iters) (.lit 1))] })))
    (.leaf (.reverted (.error "over"))))

theorem bump_not_wrong (ev : List EventDecl) (tbl : FunctionTable) :
    eraseLoopStmt (env ev tbl) (2 ^ 256 + 8) bumpFn.body (initState bumpFn) ≠ some wrongBr := by
  rw [bump_erased]
  decide

/-- Too little fuel: the loop needs `loopFuel` more than its body. -/
theorem short_fuel (ev : List EventDecl) (tbl : FunctionTable) :
    eraseLoopStmt (env ev tbl) (2 ^ 256 + 4) bumpFn.body (initState bumpFn) = none := rfl

/-- Without the update the counter does not step: no closed form. -/
theorem no_update (ev : List EventDecl) (tbl : FunctionTable) :
    eraseLoopStmt (env ev tbl) (2 ^ 256 + 8)
      (.block [s1, .block [s2, .block [s3, .forLoop .skip cnd .skip body]]]) (initState bumpFn) = none := rfl

/-- A body that adds two to `count` is not a step of one. -/
theorem adds_two (ev : List EventDecl) (tbl : FunctionTable) :
    eraseLoopStmt (env ev tbl) (2 ^ 256 + 8)
      (.block [s1, .block [s2, .block [s3, .forLoop .skip cnd post
        (.block [.exprStmt (.incDec .add true (some (.uint 256)) (.storageRead .header "count" [])),
          .exprStmt (.incDec .add true (some (.uint 256)) (.storageRead .header "count" []))])]]])
      (initState bumpFn) = none := rfl

/-- `while` loops are outside the shape. -/
theorem while_none (ev : List EventDecl) (tbl : FunctionTable) :
    eraseLoopStmt (env ev tbl) (2 ^ 256 + 8)
      (.block [s1, .block [s2, .block [s3, .whileLoop cnd (.block [body, post])]]])
      (initState bumpFn) = none := rfl

end Verify.LoopSource.Equiv.EraseLoopCounter

/-- info: 'Verify.LoopSource.Equiv.EraseLoopCounter.bump_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Equiv.EraseLoopCounter.bump_runs

/-- info: 'Verify.LoopSource.Equiv.EraseLoopCounter.bump_runs_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Equiv.EraseLoopCounter.bump_runs_checked

/-- info: 'Verify.LoopSource.Equiv.EraseLoopCounter.bump_not_wrong' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Verify.LoopSource.Equiv.EraseLoopCounter.bump_not_wrong
