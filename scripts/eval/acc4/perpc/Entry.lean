import W1Proofs.Tactic

/-! Bench only: block-entry equations for sym_exec.

`sym_exec` evaluates scheduled EVM IR by unfolding `EVM.Program.exec` instruction by instruction
on every path. Here the first time a path enters a block `b` with instructions `instrs` and a
stack of `n` words, the same dsimp set evaluates `exec o call b instrs [x₁, …, xₙ] s` once
over fresh variables, and the result, abstracted over `o call x₁ … xₙ s`, is the block's
equation for that entry height. Later entries with the same key (another path, or the other
program holding an identical block) instantiate it instead of running the block again. The
rewrite is definitional, as every step of `sym_eval` is, so the proof the kernel checks is still
a definitional unfolding: nothing is assumed and no lemma is added. -/

open Lean Meta Simp

namespace SolarTV.Eval.PerPC

structure Key where
  block : Nat
  height : Nat
  instrs : Expr
deriving BEq, Hashable

initialize summaries : IO.Ref (Std.HashMap Key Expr) ← IO.mkRef {}
initialize computing : IO.Ref Bool ← IO.mkRef false
/-- Entries answered from the cache, entries evaluated, entries left to plain unfolding. -/
initialize counts : IO.Ref (Nat × Nat × Nat) ← IO.mkRef (0, 0, 0)
/-- Time spent evaluating block entries, in nanoseconds. -/
initialize evalNanos : IO.Ref Nat ← IO.mkRef 0

/-- The words of a stack spelled out as x₁ :: … :: xₙ :: [], with the list's universe and type. -/
partial def stackWords? (e : Expr) (acc : Array Expr := #[]) : Option (Array Expr × List Level × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``List.cons 3 then
    stackWords? e.appArg! (acc.push e.appFn!.appArg!)
  else if e.isAppOfArity ``List.nil 1 then
    some (acc, e.getAppFn.constLevels!, e.appArg!)
  else none

def mkStack (us : List Level) (α : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x t => mkApp3 (mkConst ``List.cons us) α x t) (mkApp (mkConst ``List.nil us) α)

dsimproc_decl blockEntry (EVM.Program.exec _ _ _ _ _ _) := fun e => do
  if (← computing.get) then return .continue
  let_expr EVM.Program.exec o call b instrs stack s := e | return .continue
  let some bn ← Nat.fromExpr? b | return .continue
  let instrs := instrs.consumeMData
  unless instrs.isAppOfArity ``List.cons 3 do return .continue
  if instrs.hasFVar || instrs.hasMVar then return .continue
  let some (ws, us, α) := stackWords? stack
    | counts.modify (fun (h, m, u) => (h, m, u + 1)); return .continue
  let key : Key := { block := bn, height := ws.size, instrs }
  let f ← match (← summaries.get)[key]? with
    | some f => counts.modify (fun (h, m, u) => (h + 1, m, u)); pure f
    | none =>
      counts.modify (fun (h, m, u) => (h, m + 1, u))
      let oTy ← inferType o
      let cTy ← inferType call
      let sTy ← inferType s
      let f ← withLocalDeclD `o oTy fun o' =>
        withLocalDeclD `call cTy fun c' =>
        withLocalDeclD `s sTy fun s' =>
        withLocalDeclsDND (Array.ofFn fun (i : Fin ws.size) => (Name.mkSimple s!"x{i.val}", α)) fun xs => do
          let entry := mkAppN e.getAppFn #[o', c', b, instrs, mkStack us α xs, s']
          computing.set true
          let t0 ← IO.monoNanosNow
          let r ← try Simp.dsimp entry finally computing.set false
          let t1 ← IO.monoNanosNow
          evalNanos.modify (· + (t1 - t0))
          mkLambdaFVars (#[o', c'] ++ xs ++ #[s']) r
      summaries.modify (·.insert key f)
      pure f
  return .visit (f.beta (#[o, call] ++ ws ++ #[s]))

elab "#block_entry_counts" : command => do
  let (h, m, u) ← counts.get
  logInfo m!"block entries: {h} from cache, {m} evaluated, {u} left to unfolding; {(← summaries.get).size} equations; evaluating them took {(← evalNanos.get) / 1000000} ms"

end SolarTV.Eval.PerPC
