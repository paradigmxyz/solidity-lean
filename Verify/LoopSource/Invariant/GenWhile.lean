import Verify.LoopSource.Invariant.Final
import Verify.Phase3.Route.GenInfer

/-!
# The `while` route's generator (untrusted)

For a function whose body `eraseLoopStmt` does not erase because its loop is a `while` loop, the
driver (solar's `tools/certify/loop_cuts.py`) runs these steps on the same `GenObl.Config` it gives
`GenObl.run`:

* `probe cfg src mir`: proposes the loop's data `WhileData` and writes two JSON files for
  `loop_infer.py`:
  - **what is proposed, not recomputed**: `S1` (the state at the loop, found by walking the body as
    `eraseWhile` does), `slots` (always `[]` here: a loop that writes storage is refused), `k` (the
    least body fuel at which the body erases), and `exit` (the words after the loop, fitted to
    concrete runs of the erased step from candidate words: the words before the loop, the call's
    words, `0` and `1`);
  - **what is computed from the statement**: `c`, `gs` and `S2`, the condition's and the body's
    erasure at the header `S1` and `slots` give (`check` compares them by equality when the kernel
    evaluates `eraseWhile`; it never reads `exit`, which only the obligations justify);
  - `src`: the source loop as a cut-point system over the source header's words (entry: the words
    before the loop; iteration: a zero condition exits with the header words written to slots
    `0, 1, …`, a guard that fires reverts, else the step), with the target tree writing the `exit`
    words, so `loop_infer.py`'s obligations are `whileSeqs`'s;
  - `mir`: the cut check's leaves with **the tree of the source's own `eraseWhile` erasure**
    (`"tree_source": "while"`), as `GenInfer.exportLeaves` does for the counted route.
* `emit cfg Is μs I μ`: with the source invariant `Is`, `μs` and the MIR invariant `I`, `μ` (both
  untrusted, from `loop_infer.py` or an annotation), writes the obligation modules: `GenObl.run`'s
  Data, V0..Vk and Obl over `allSeqsW`, with the source facts in Obl: `whileOf_eq` (the erasure with
  the proposed data, by `kernel_rfl`), `src_seqs` and `src_valid` (the source loop's sequents and
  their `wordnorm` proofs), `loop_tree` and `same`. Its JSON line names the route `while-inferred`.

Nothing here is trusted: every fact the modules state is checked by the kernel when they build.
-/

namespace Verify.LoopSource.Invariant.GenWhile
open SolidCore.Solidity.Source SolidCore.Refinement.Generic SolidCore.Refinement.Generic.Loop
open Verify.LoopSource.Equiv
open Verify.LoopSource.Equiv.Inv (F Seq traceVals callsOf holdsB emitSeqs)
open Verify.LoopSource.Equiv.GenObl (Config refuse loopTree)
open Verify.Phase3.Route.GenInfer (q arr wj tj kj lj replaceOnce)
open Verify.LoopSource.Invariant (WhileData eraseStep eraseWhile whileSeqs)

/-! ## Proposing the loop's data -/

/-- The state, condition and body at the first `while` loop, walking the statements as
`eraseWhile` does (a block pushes a scope and pops it after; a statement before the loop must erase
by `eraseStep` to guards before one normal end); `.inr S`: the list ends normally in `S`. -/
def findLoop (E : EraseEnv) (k : Nat) : Nat → List Stmt → SymState →
    Option (Sum (SymState × Expr × Stmt) SymState)
  | 0, _, _ => none
  | _ + 1, [], S => some (.inr S)
  | n + 1, s :: rest, S =>
    match s with
    | .whileLoop c b => some (.inl (S, c, b))
    | .block ss =>
      match findLoop E k n ss S.push with
      | some (.inl x) => some (.inl x)
      | some (.inr S') => findLoop E k n rest S'.pop
      | none => none
    | s => do
      let b ← eraseStep E k s S
      let (_, S') ← splitG b
      findLoop E k n rest S'

/-- The words fresh word `j` steps to and holds before the loop, as lists. -/
def stepsOf (wd : WhileData) : List WExpr := (List.range wd.len).map wd.step
def initsOf (wd : WhileData) : List WExpr := (List.range wd.len).map wd.θ0

/-- The data the statement gives at the state `S1`, with no exit words yet. -/
def dataOf (E : EraseEnv) (S1 : SymState) (cnd : Expr) (body : Stmt) : Except String WhileData := do
  let wd0 : WhileData := { S1, slots := [], k := 0, c := .lit 0, gs := [], S2 := S1, exit := [] }
  let H := wd0.H E
  let c ← match eraseExpr E.fields H cnd with
    | some ([], c) => pure c
    | some (_ :: _, _) => throw "the loop's condition has overflow guards: the while route takes a condition that erases with none"
    | none => throw "the loop's condition does not erase at the header"
  let some (k, gs, S2) := (List.range 65).findSome? fun k => do
      let b ← eraseStep E k body H
      let (gs, S2) ← splitG b
      pure (k, gs, S2)
    | throw "the loop's body does not erase at the header to overflow guards before one normal end (eraseStep: x++, x--, assignments, no nested loop, break, continue, return or revert)"
  let wd := { wd0 with k, c, gs, S2 }
  if S2 != instS (wd.base E) wd.len wd.step H then
    throw "the body's end is not the header with its own words (the loop writes storage or declares a local outside a block)"
  pure wd

/-- The header words after at most `m` concrete iterations from the words `v`. -/
def iter (E : EraseEnv) (wd : WhileData) (ρ : Val) : Nat → List Nat → Option (List Nat)
  | 0, _ => none
  | m + 1, v =>
    let σ := extV ρ (wd.base E) wd.len (fun j => v.getD j 0)
    if wd.c.eval σ = 0 then some v
    else if wd.gs.any (fun g => g.eval σ != 0) then none
    else iter E wd ρ m (stepsOf wd |>.map (·.eval σ))

/-- The header words the loop ends with from the call `ρ`: `none` when a guard fires or the loop
runs longer than `fuel`. -/
def simulate (E : EraseEnv) (wd : WhileData) (ρ : Val) (fuel : Nat) : Option (List Nat) :=
  iter E wd ρ fuel (initsOf wd |>.map (·.eval ρ))

/-- The header words after exactly `m` steps from the call `ρ` (stopping at the exit). -/
def stepN (E : EraseEnv) (wd : WhileData) (ρ : Val) : Nat → List Nat → List Nat
  | 0, v => v
  | m + 1, v =>
    let σ := extV ρ (wd.base E) wd.len (fun j => v.getD j 0)
    if wd.c.eval σ = 0 || wd.gs.any (fun g => g.eval σ != 0) then v
    else stepN E wd ρ m (stepsOf wd |>.map (·.eval σ))

/-- Small calls of `n` argument words. -/
def smallCalls (n : Nat) : List Val :=
  let ws : List Nat := [0, 1, 2, 3, 5, 9]
  let argss := (List.range n).foldr (fun _ acc => ws.flatMap fun w => acc.map (w :: ·)) [[]]
  argss.map fun as => { args := as, store := fun _ => 0, hash := fun _ _ => 0, caller := 0 }

/-- **The exit words**, fitted to concrete runs: for each fresh word, the first candidate (its word
before the loop, the other words before the loop, `0`, `1`, the call's words) that every
terminating run ends with. -/
def exitOf (E : EraseEnv) (wd : WhileData) : Except String (List WExpr) := do
  let runs := (smallCalls (wd.base E)).filterMap fun ρ =>
    (simulate E wd ρ 64).map fun v => (ρ, v)
  if runs.length < 3 then
    throw s!"only {runs.length} small calls end the loop within 64 iterations: no exit words to fit"
  let cands (j : Nat) : List WExpr :=
    [wd.θ0 j] ++ initsOf wd ++ [.lit 0, .lit 1] ++ (List.range (wd.base E)).map WExpr.arg
  (List.range wd.len).mapM fun j =>
    match (cands j).find? fun e => runs.all fun (ρ, v) => e.eval ρ == v.getD j 0 with
    | some e => pure e
    | none => throw s!"no candidate exit word fits header word {j} on every concrete run"

/-- The function's erasure environment and function, as the generator needs them. -/
def envOf? (cfg : Config) : Except String (EraseEnv × FunctionDef) := do
  let some c := cfg.contract?.toOption | throw "the source does not type-check"
  let some fn := c.core.findFunctionBySelector? cfg.sel
    | throw "the checked contract has no function at the selector"
  let some ws := widthsOf fn.params fn.paramAbiCleanups
    | throw "the function's parameters are not words (widthsOf is none)"
  if fn.params.length != cfg.nargs then
    throw s!"the function has {fn.params.length} parameters, not the cut's {cfg.nargs}"
  pure ({ envOf c.core with facts := argFacts ws 0 }, fn)

/-- **The loop's data**, its erasure and its tree, all checked here as the kernel will check them. -/
def whileData (cfg : Config) : Except String (EraseEnv × FunctionDef × WhileData × Br × Tree) := do
  let (E, fn) ← envOf? cfg
  let (S1, cnd, body) ← match findLoop E 64 64 [fn.body] (initState fn) with
    | some (.inl x) => pure x
    | some (.inr _) => throw "the function's body has no while loop the walk reaches"
    | none => throw "a statement before the while loop does not erase to guards before one normal end"
  let wd0 ← dataOf E S1 cnd body
  let exit ← exitOf E wd0
  let wd := { wd0 with exit }
  if !Verify.LoopSource.Invariant.check E wd cnd body then
    throw "the loop's data does not check (Invariant.check)"
  let some (n, b, Te) := Verify.LoopSource.Invariant.Final.whileOf cfg.contract? cfg.sel cfg.fuel wd
    | throw (if (eraseWhile E wd (cfg.fuel + 2 ^ 257) fn.body (initState fn)).isSome then
        s!"eraseWhile needs more fuel than the statement's {cfg.fuel} (body fuel {wd.k})"
      else "eraseWhile is none: a statement after the loop, a second loop or the loop's state is outside the erasure")
  if n != cfg.nargs then throw "whileOf's arity is not the cut's"
  pure (E, fn, wd, b, Te)

/-! ## The two exports -/

/-- The header's names, in its order. -/
def namesOf (S : SymState) : List String := S.scopes.flatMap (·.map (·.1))

/-- **The source loop as a cut-point system** for `loop_infer.py`. -/
def srcJson (cfg : Config) (E : EraseEnv) (fn : FunctionDef) (wd : WhileData) : String :=
  let b := wd.base E
  let len := wd.len
  let hdr : Writes := (List.range len).map fun j => (.lit j, .arg (b + j))
  let tgt : Writes := (List.range len).map fun j => (.lit j, wd.exitθ j)
  let le : List (Facts × Out) := [(E.facts, .back (initsOf wd))]
  let gli : List (Facts × Out) := (List.range wd.gs.length).map fun i =>
    ([(wd.c, true)] ++ (wd.gs.take i).map (·, false) ++ [(wd.gs.getD i (.lit 0), true)],
      .exit (.halt false [] [] []))
  let li : List (Facts × Out) := [([(wd.c, false)], .exit (.halt true [] hdr []))] ++ gli ++
    [([(wd.c, true)] ++ wd.gs.map (·, false), .back (stepsOf wd))]
  let cases : List Facts := [[(wd.c, true)], [(wd.c, false)]]
  let names := arr ((namesOf wd.S1).map q)
  let params := arr (fn.params.map fun p => q p.name)
  s!"\{\"format\":\"loop leaves 1\",\"tree_source\":\"while source\",\"fn\":{q fn.name},\"sel\":{cfg.sel},\"n\":{b},\"nhw\":{len},\"names\":{names},\"params\":{params},\"cases\":{arr (cases.map kj)},\"le\":{lj le},\"li\":{lj li},\"T\":{tj (.halt true [] tgt [])},\"exit\":{arr (wd.exit.map wj)},\"steps\":{arr ((stepsOf wd).map wj)},\"inits\":{arr ((initsOf wd).map wj)}}"

/-- **Probe**: the loop's data, the source system and the MIR leaves with the while erasure's tree. -/
def probe (cfg : Config) (srcPath mirPath : String) : IO UInt32 := do
  match whileData cfg with
  | .error why => refuse why
  | .ok (E, fn, wd, _, Te) =>
    let some (le, li) := cfg.cut.check .off cfg.stage0 cfg.sel cfg.nargs
      | refuse "cut.check is none: the certificate does not match the MIR"
    IO.FS.writeFile srcPath (srcJson cfg E fn wd ++ "\n")
    let T := loopTree Te
    let j := s!"\{\"format\":\"loop leaves 1\",\"tree_source\":\"while\",\"fn\":{q fn.name},\"sel\":{cfg.sel},\"n\":{cfg.nargs},\"nhw\":{cfg.cut.nhw},\"cases\":{arr (cfg.cut.cases.map kj)},\"le\":{lj le},\"li\":{lj li},\"T\":{tj T}}"
    IO.FS.writeFile mirPath (j ++ "\n")
    IO.println s!"\{\"format\":\"while probe 1\",\"base\":{wd.base E},\"len\":{wd.len},\"k\":{wd.k},\"guards\":{wd.gs.length},\"exit\":{arr (wd.exit.map wj)},\"names\":{arr ((namesOf wd.S1).map q)},\"src\":{q srcPath},\"mir\":{q mirPath}}"
    return 0

/-! ## Emission -/

/-- The source facts of the Obl module: the data, its erasure, the source sequents and their proofs,
and the sequents' tree. Every name is qualified: the module opens `Verify.LoopSource.Equiv`. The data
is printed on one line: `reprStr`'s layout of a nested structure breaks its fields below the inner
structure's first field, which the structure-instance parser refuses. -/
def srcExt (cfg : Config) (wd : WhileData) (n : Nat) (b : Br) (Te : Tree) (Is : List F) (μs : WExpr)
    (ss0 : List Seq) : String :=
  let W := s!"Verify.LoopSource.Invariant.Final.whileOf ({cfg.contractName}) {cfg.sel} {cfg.fuel} wd"
  let S := s!"Verify.LoopSource.Invariant.Final.srcSeqsOf ({cfg.contractName}) {cfg.sel} wd Is μs"
  let defs := String.intercalate "\n" ((ss0.zipIdx).map fun (s, i) =>
    s!"def sq{i} : Verify.LoopSource.Equiv.Inv.Seq := {reprStr s}\n")
  let pfs := String.intercalate "\n" ((ss0.zipIdx).map fun (_, i) =>
    s!"theorem sv{i} : Verify.LoopSource.Equiv.Inv.Seq.Valid sq{i} := by\n  simp only [sq{i}, Verify.LoopSource.Equiv.Inv.Seq.Valid]\n  first\n    | wordnormW\n    | wordnorm\n    | (intro σ _\n       simp [Verify.LoopSource.Equiv.Inv.F.Holds])\n")
  let lit := "[" ++ String.intercalate ", " ((List.range ss0.length).map fun i => s!"sq{i}") ++ "]"
  let conj := (List.range ss0.length).foldr (fun i acc => s!"List.forall_mem_cons.mpr ⟨sv{i}, {acc}⟩")
    "fun _ h => absurd h List.not_mem_nil"
  "/-- The loop's data (proposed: `S1`, `slots`, `k`, `exit`; recomputed by `check` inside `eraseWhile`: `c`, `gs`, `S2`). -/\n" ++
  s!"def wd : Verify.LoopSource.Invariant.WhileData :=\n  {(repr wd).pretty 1000000}\n\n" ++
  "/-- The function's body, erased by `eraseWhile` with the loop's data at the statement fuel. -/\n" ++
  s!"def br : SolidCore.Refinement.Generic.Br := {reprStr b}\n\n" ++
  "/-- The erased body's tree. -/\n" ++
  s!"def Te : SolidCore.Refinement.Generic.Tree := {reprStr Te}\n\n" ++
  s!"def whileV : Option (Nat × SolidCore.Refinement.Generic.Br × SolidCore.Refinement.Generic.Tree) :=\n  {W}\n\n" ++
  s!"kernel_rfl while_eq whileV (some ({n}, br, Te))\n\n" ++
  "/-- **The source premise of the join**: the imported function's arity, its body's `eraseWhile` erasure and its tree. -/\n" ++
  s!"theorem whileOf_eq : {W} = some ({n}, br, Te) := while_eq\n\n" ++
  "/-- The source loop's invariant and measure over the source header's words (untrusted until `src_valid`). -/\n" ++
  s!"def Is : List Verify.LoopSource.Equiv.Inv.F := {reprStr Is}\n\n" ++
  s!"def μs : SolidCore.Refinement.Generic.WExpr := {reprStr μs}\n\n" ++
  defs ++ "\n" ++
  s!"def srcSeqs : List Verify.LoopSource.Equiv.Inv.Seq := {lit}\n\n" ++
  s!"def srcV : Option (List Verify.LoopSource.Equiv.Inv.Seq) :=\n  {S}\n\n" ++
  "kernel_rfl src_eq srcV (some srcSeqs)\n\n" ++
  "/-- **The source loop's sequents** (`whileSeqs`: initiation, exit, guards, preservation, descent). -/\n" ++
  s!"theorem src_seqs : {S} = some srcSeqs := src_eq\n\n" ++
  pfs ++ "\n" ++
  s!"theorem src_valid : ∀ s ∈ srcSeqs, Verify.LoopSource.Equiv.Inv.Seq.Valid s :=\n  show ∀ s ∈ {lit}, Verify.LoopSource.Equiv.Inv.Seq.Valid s from\n  {conj}\n\n" ++
  "/-- The sequents' tree `T` is the erased tree simplified. -/\n" ++
  "theorem loop_tree : Verify.LoopSource.Equiv.GenObl.loopTree Te = T :=\n" ++
  "  Option.some.inj (treeBeq_eq (by decide +kernel))\n\n" ++
  "/-- **The erased tree and the sequents' tree observe alike on every call.** -/\n" ++
  "theorem same : ∀ ρ : SolidCore.Refinement.Generic.Val, ρ.Ok → (Te.eval ρ).obs = (T.eval ρ).obs :=\n" ++
  "  fun ρ _ => loop_tree ▸ Verify.LoopSource.Equiv.GenObl.obs_loopTree Te ρ\n\n"

/-- The index of a sequent a probe valuation refutes. -/
def refutedAt (ss : List Seq) (probe : List Val) : Option Nat :=
  (ss.zipIdx.filter fun (s, _) => probe.any fun σ =>
    s.1.all (holdsB σ) && match s.2 with | some goal => !holdsB σ goal | none => true).head?.map (·.2)

/-- **Emit** the obligation modules for the source invariant `Is`, `μs` and the MIR invariant `I`, `μ`. -/
def emit (cfg : Config) (Is : List F) (μs : WExpr) (I : List F) (μ : WExpr) : IO UInt32 := do
  let (E, _, wd, b, Te) ← match whileData cfg with
    | .error why => do let _ ← refuse why; return 2
    | .ok x => pure x
  let some ss0 := whileSeqs E wd Is μs
    | refuse "whileSeqs is none: a fact or an exit word mentions a header word"
  if (Verify.LoopSource.Invariant.Final.srcSeqsOf cfg.contract? cfg.sel wd Is μs) != some ss0 then
    return ← refuse "srcSeqsOf disagrees with the sequents computed here"
  -- Header valuations of small calls after 0 to 7 concrete steps.
  let srcProbe := (smallCalls (wd.base E)).flatMap fun ρ =>
    (List.range 8).map fun m =>
      let v := stepN E wd ρ m (initsOf wd |>.map (·.eval ρ))
      extV ρ (wd.base E) wd.len (fun j => v.getD j 0)
  if let some i := refutedAt ss0 srcProbe then
    return ← refuse s!"source sequent {i} of the proposed source invariant has a concrete counterexample"
  let some (le, li) := cfg.cut.check .off cfg.stage0 cfg.sel cfg.nargs
    | refuse "cut.check is none: the certificate does not match the MIR"
  let T := loopTree Te
  let some ss := Verify.Phase3.Infer.allSeqsW cfg.nargs cfg.cut.cases T le li I μ
    | refuse "allSeqsW is none for the proposed MIR invariant and measure"
  let calls := callsOf cfg.nargs Verify.LoopSource.Equiv.GenObl.slots
  let vals := traceVals cfg.nargs le li calls 20
  if let some i := refutedAt ss (calls ++ vals) then
    return ← refuse s!"sequent {i} of the proposed MIR invariant has a traced counterexample"
  let chk := s!"{cfg.cutName}.check .off {cfg.stage0Name} {cfg.sel} {cfg.nargs}"
  let ext := srcExt cfg wd cfg.nargs b Te Is μs ss0
  let mods := emitSeqs (cfg.imports ++ ["Verify.LoopSource.Equiv.EmitSeq", "Verify.Phase3.Infer.SeqW"])
    (["Verify.LoopSource.Invariant.Final", "Verify.Phase3.Infer.SeqW"] ++ cfg.imports) cfg.pre cfg.ns
    "" chk "some (Verify.LoopSource.Equiv.GenObl.loopTree Te)" cfg.nargs s!"{cfg.cutName}.cases" le li T
    I μ ss cfg.files (ext? := some ext) (treeBy? := some "congrArg some loop_tree")
  let mut out : List (String × String) := []
  for (stem, text) in mods do
    if stem == cfg.pre ++ "Obl" then
      let some t1 := replaceOnce text s!"theorem seqs : allSeqs {cfg.nargs} " s!"theorem seqs : Verify.Phase3.Infer.allSeqsW {cfg.nargs} "
        | return ← refuse "emitSeqs's Obl module has no allSeqs sequents theorem to restate"
      let some t2 := replaceOnce t1 "  obl_of_seqs seqs valid" "  Verify.Phase3.Infer.obl_of_seqsW seqs valid"
        | return ← refuse "emitSeqs's Obl module has no obl_of_seqs proof to restate"
      out := out ++ [(stem, t2)]
    else if (stem.drop cfg.pre.length).startsWith "V" then
      out := out ++ [(stem, text.replace "  first\n    | wordnorm\n" "  first\n    | wordnormW\n    | wordnorm\n")]
    else
      out := out ++ [(stem, text)]
  for (stem, text) in out do
    let f := System.FilePath.mk cfg.root / (stem ++ ".lean")
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  let rel := out.map (·.1)
  let qq (s : String) : String := "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""
  let measure := (reprStr μ).replace "\n" " "
  IO.println s!"\{\"format\":\"loop obligations 1\",\"route\":\"while-inferred\",\"modules\":[{String.intercalate "," (rel.map qq)}],\"measure\":{qq measure},\"sequents\":{ss.length},\"source_sequents\":{ss0.length}}"
  return 0

end Verify.LoopSource.Invariant.GenWhile
