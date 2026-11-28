import Verify.LoopSource.Equiv.EmitSeq
import Verify.LoopSource.Equiv.Emit
import SolidCore.Refinement.Generic.SourceCall
import SolidCore.Refinement.Generic.LoopRun
import Verify.LoopSource.Proof.EraseLoop

/-!
# The loop-obligation generator the certify driver runs (untrusted)

`run cfg` writes, under `cfg.root`, the modules `<pre>Data`, `<pre>V0`..`<pre>Vk` and `<pre>Obl`
for one loop-carrying function: the leaves of its cut-point check, the source tree, the inferred
invariant and measure, the sequents and their `wordnorm` proofs, and the theorems `leaves`,
`tree`, `seqs`, `valid` and `obl` in `cfg.ns`. Nothing here is trusted: every fact the modules
state is checked by the kernel when they are built.

The source tree is `brTree fn (argFacts ws 0) b` for the function `fn` at `cfg.sel` in the checked
contract and a body tree `b`, from one of two routes:

* **the erasure** (`cfg.summary? = none`, the default): `b` is `eraseLoopStmt` of the body at the
  statement fuel `cfg.fuel` (one counted `for` loop per body, `Proof/EraseLoop.lean`). The generated
  module proves the erasure by `kernel_rfl` (`erased_eq`) and from it `erased : Erased …`, the
  source premises `EraseLoopJoin.GeneratedTarget` takes (the arity, the erasure and its tree);
  `Erased.runs` gives the body's `BodyRuns` by `bodyRuns_of_eraseLoop`. The sequents are stated over
  `loopTree` of the erased tree, which observes alike on every call (`same`, the join's `hsame`).
  A body outside the erasure's shape is refused.
* **a body summary** (`cfg.summary? = some sm`): `b` is the summary's tree, checked against the
  imported source. The generator refuses when the summary's shape (fields, function, body) is not
  the imported contract's; the generated module proves `shape_eq` and `runs`.

Either way a sequent with a traced counterexample is refused. It prints one JSON line
`{"format":"loop obligations 1","modules":[…],"measure":"…"}` (module stems relative to
`cfg.root`) and returns 0, or returns 2 with the reason on stderr when the cut-point check, the
source tree or the sequents are none, or no measure is accepted.
-/

namespace Verify.LoopSource.Equiv.GenObl
open SolidCore.Refinement.Generic Verify.LoopSource.Equiv Verify.LoopSource.Equiv.Inv
open SolidCore.Refinement.Generic.Loop
abbrev FunctionDef := SolidCore.Solidity.Source.FunctionDef

abbrev Checked := Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract

/-! ## Body summaries, checked against the imported source

A body summary `b` is the loop route's description of a function's body: every run of the body ends
at one of `b`'s leaves (`BodyRuns`). It is only usable for the body it was proved for. `Summary`
ties it to that body through the **shape** the proof depends on: the contract's storage fields and
the function at the selector, whose `body` is the source the summary was proved for. A summary's
theorem (`SummaryOk`) proves `BodyRuns` for every contract of that shape; the generated module
proves, in the kernel, that the imported contract has that shape (`shape_eq`, by `kernel_rfl`), and
from both that the imported function's body runs to `b` (`runs`, by `runs_of_summary`). -/

/-- The fields and the function at `sel` of a checked contract. -/
def shapeOfC (c : SolidCore.Solidity.TypeCheck.CheckedContract) (sel : Nat) :
    Option (List SolidCore.Solidity.Source.StorageField × FunctionDef) :=
  (c.core.findFunctionBySelector? sel).map (c.core.storageFields, ·)

def shapeOf (c? : Checked) (sel : Nat) : Option (List SolidCore.Solidity.Source.StorageField × FunctionDef) :=
  c?.toOption.bind (shapeOfC · sel)

/-- **What a summary proves**: on every contract whose fields and function at `sel` are `s`, the
function's body runs to `b` from fuel `m` on. -/
def SummaryOk (sel m : Nat) (s : List SolidCore.Solidity.Source.StorageField × FunctionDef) (b : Br) : Prop :=
  ∀ c : SolidCore.Solidity.TypeCheck.CheckedContract, shapeOfC c sel = some s →
    ∀ ws, widthsOf s.2.params s.2.paramAbiCleanups = some ws →
      ∀ fuel, m ≤ fuel → BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel s.2 b

/-- **The imported function's body runs to `b`.** -/
def Runs (c? : Checked) (sel m : Nat) (b : Br) : Prop :=
  ∀ c, c? = .ok c → ∀ fn ws, c.core.findFunctionBySelector? sel = some fn →
    widthsOf fn.params fn.paramAbiCleanups = some ws →
      ∀ fuel, m ≤ fuel → BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b

/-- **A summary applies to an imported contract of its shape.** -/
theorem runs_of_summary {c? : Checked} {sel m : Nat} {s} {b : Br} (h : SummaryOk sel m s b)
    (hs : shapeOf c? sel = some s) : Runs c? sel m b := by
  rintro c rfl fn ws hf hw fuel hfu
  have hs' : shapeOfC c sel = some s := hs
  obtain rfl : (c.core.storageFields, fn) = s := by simpa [shapeOfC, hf] using hs'
  exact h c hs' ws hw fuel hfu

/-- The source tree of a function from its body summary `b`. -/
def treeOfFn (fn : FunctionDef) (b : Br) : Option Tree := do
  let ws ← widthsOf fn.params fn.paramAbiCleanups
  brTree fn (argFacts ws 0) b

/-- The source tree of the function at `sel` of a checked contract, from its body summary `b`. -/
def treeOf (c? : Checked) (sel : Nat) (b : Br) : Option Tree :=
  (shapeOf c? sel).bind fun s => treeOfFn s.2 b

theorem treeOf_of_shape {c? : Checked} {sel : Nat} {s} (b : Br) (hs : shapeOf c? sel = some s) :
    treeOf c? sel b = treeOfFn s.2 b := by
  simp only [treeOf, hs, Option.bind_some]

/-! ## The erasure route: the source tree from `eraseLoopStmt` -/

/-- The arity, the erasure and the source tree of the function at `sel` of a checked contract, at
fuel `fuel`: `none` when there is no such function or its body is outside the erasure's shape. -/
def erasedOf (c? : Checked) (sel fuel : Nat) : Option (Nat × Br × Tree) := do
  let c ← c?.toOption
  let fn ← c.core.findFunctionBySelector? sel
  let ws ← widthsOf fn.params fn.paramAbiCleanups
  let b ← eraseLoopStmt { envOf c.core with facts := argFacts ws 0 } fuel fn.body (initState fn)
  let T ← brTree fn (argFacts ws 0) b
  pure (fn.params.length, b, T)

/-- **What the erasure gives the source join**: for the imported contract's function at `sel`, its
arity is `n`, its body erases (`eraseLoopStmt`, at fuel `fuel`) to `b`, and `b`'s tree is `T`:
the premises `h` and `hT` of `EraseLoopJoin.GeneratedTarget`, and the arity its cut check names. -/
def Erased (c? : Checked) (sel fuel n : Nat) (b : Br) (T : Tree) : Prop :=
  ∀ c, c? = .ok c → ∀ fn ws, c.core.findFunctionBySelector? sel = some fn →
    widthsOf fn.params fn.paramAbiCleanups = some ws →
      fn.params.length = n ∧
      eraseLoopStmt { envOf c.core with facts := argFacts ws 0 } fuel fn.body (initState fn) = some b ∧
      brTree fn (argFacts ws 0) b = some T

/-- **The computed erasure is the imported function's.** -/
theorem erased_of {c? : Checked} {sel fuel n : Nat} {b : Br} {T : Tree}
    (h : erasedOf c? sel fuel = some (n, b, T)) : Erased c? sel fuel n b T := by
  rintro c rfl fn ws hf hw
  cases he : eraseLoopStmt { envOf c.core with facts := argFacts ws 0 } fuel fn.body (initState fn) with
  | none => simp [erasedOf, Except.toOption, hf, hw, he] at h
  | some b' =>
    cases ht : brTree fn (argFacts ws 0) b' with
    | none => simp [erasedOf, Except.toOption, hf, hw, he, ht] at h
    | some T' =>
      simp only [erasedOf, Except.toOption, hf, hw, he, ht, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, ?_, ?_⟩ <;> first | rfl | assumption

/-- **The erased function's body runs to the erasure** (`bodyRuns_of_eraseLoop`): the premise `hb`
of `loop_stage`. -/
theorem Erased.runs {c? : Checked} {sel fuel n : Nat} {b : Br} {T : Tree} (h : Erased c? sel fuel n b T) :
    ∀ c, c? = .ok c → ∀ fn ws, c.core.findFunctionBySelector? sel = some fn →
      widthsOf fn.params fn.paramAbiCleanups = some ws →
        BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b :=
  fun c hc fn ws hf hw => bodyRuns_of_eraseLoop (h c hc fn ws hf hw).2.1

/-! ## The sequents' tree: the erased tree, simplified

`eraseLoopStmt`'s closed form counts the iterations of `for (i = c; i < b; i++)` as
`sel (lt c b) (sub b c) 0`, which `wordnorm` does not decide in the sequents. The sequents are
stated over `loopTree T` instead: every word of the erased tree with `sub x 0` rewritten to `x` and
`sel (lt 0 x) x 0` to `x` (`simpW`, bottom up), then `Tree.canon` (constants folded, branches
already decided on the path taken). It gives every call the same result (`eval_loopTree`), which
is the premise `hsame` of `EraseLoopJoin.GeneratedTarget` (`obs_loopTree`). -/

/-- `sub x 0` is `x`, and `sel (lt 0 x) x 0` is `x`, bottom up. -/
def simpW : WExpr → WExpr
  | .un op a => .un op (simpW a)
  | .bin op a b =>
    if op = .sub ∧ simpW b = .lit 0 then simpW a else .bin op (simpW a) (simpW b)
  | .sinit k => .sinit (simpW k)
  | .sel c a b =>
    if simpW c = .bin .lt (.lit 0) (simpW a) ∧ simpW b = .lit 0 then simpW a
    else .sel (simpW c) (simpW a) (simpW b)
  | .hash a b => .hash (simpW a) (simpW b)
  | e => e

theorem eval_simpW (ρ : Val) : ∀ e : WExpr, (simpW e).eval ρ = e.eval ρ
  | .lit _ => rfl
  | .arg _ => rfl
  | .init _ => rfl
  | .caller => rfl
  | .un op a => by simp only [simpW, WExpr.eval, eval_simpW ρ a]
  | .bin op a b => by
    have ha := eval_simpW ρ a
    have hb := eval_simpW ρ b
    simp only [simpW]
    split
    · rename_i h
      obtain ⟨rfl, h0⟩ := h
      have hb0 : b.eval ρ = 0 := by rw [← hb, h0]; simp [WExpr.eval]
      simp only [WExpr.eval, BinOp.eval, hb0, ha, Nat.sub_zero, Nat.add_mod_right,
        Nat.mod_eq_of_lt (a.eval_lt ρ)]
    · simp only [WExpr.eval, ha, hb]
  | .sinit k => by simp only [simpW, WExpr.eval, eval_simpW ρ k]
  | .sel c a b => by
    have hc := eval_simpW ρ c
    have ha := eval_simpW ρ a
    have hb := eval_simpW ρ b
    simp only [simpW]
    split
    · rename_i h
      obtain ⟨h1, h0⟩ := h
      have hb0 : b.eval ρ = 0 := by rw [← hb, h0]; simp [WExpr.eval]
      rw [h1] at hc
      simp only [WExpr.eval, BinOp.eval, Nat.zero_mod, ha] at hc
      simp only [WExpr.eval, hb0, ha]
      split
      · rename_i hz
        rw [← hc] at hz
        by_cases hp : 0 < a.eval ρ
        · simp [hp] at hz
        · omega
      · rfl
    · simp only [WExpr.eval, hc, ha, hb]
  | .hash a b => by simp only [simpW, WExpr.eval, eval_simpW ρ a, eval_simpW ρ b]

/-- An output byte with `simpW` applied to its word. -/
def simpO : OByte → OByte
  | .byteOf e i => .byteOf (simpW e) i
  | b => b

theorem eval_simpO (ρ : Val) : ∀ b : OByte, (simpO b).eval ρ = b.eval ρ
  | .byteOf e i => by simp only [simpO, OByte.eval, eval_simpW ρ e]
  | .lit _ => rfl

/-- A tree with `simpW` applied to every word. -/
def simpT : Tree → Tree
  | .halt ok out ws ls => .halt ok (out.map simpO) (ws.mapW simpW) (ls.map (Log.mapL simpW simpO))
  | .ite c t e => .ite (simpW c) (simpT t) (simpT e)

theorem eval_simpT (ρ : Val) : ∀ T : Tree, (simpT T).eval ρ = T.eval ρ
  | .halt ok out ws ls => by
    simp only [simpT, Tree.eval, List.map_map, Writes.store_mapW ρ simpW (eval_simpW ρ)]
    congr 2
    · funext b
      exact eval_simpO ρ b
    · congr 1
      funext l
      exact Log.eval_mapL ρ _ _ (eval_simpW ρ) (eval_simpO ρ) l
  | .ite c t e => by simp only [simpT, Tree.eval, eval_simpW ρ c, eval_simpT ρ t, eval_simpT ρ e]

/-- **The sequents' tree**: the erased tree simplified. -/
def loopTree (T : Tree) : Tree := (simpT T).canon

theorem eval_loopTree (ρ : Val) (T : Tree) : (loopTree T).eval ρ = T.eval ρ := by
  rw [loopTree, Tree.eval_canon, eval_simpT]

/-- **The erased tree and the sequents' tree observe alike on every call.** -/
theorem obs_loopTree (T : Tree) (ρ : Val) : (T.eval ρ).obs = ((loopTree T).eval ρ).obs := by
  rw [eval_loopTree]

/-- The tree of the erasure is the function's tree of `b`. -/
theorem treeOf_of_erasedOf {c? : Checked} {sel fuel n : Nat} {b : Br} {T : Tree}
    (h : erasedOf c? sel fuel = some (n, b, T)) : treeOf c? sel b = some T := by
  cases hc : c? with
  | error e => subst hc; simp [erasedOf, Except.toOption] at h
  | ok c =>
    subst hc
    cases hf : c.core.findFunctionBySelector? sel with
    | none => simp [erasedOf, Except.toOption, hf] at h
    | some fn =>
      cases hw : widthsOf fn.params fn.paramAbiCleanups with
      | none => simp [erasedOf, Except.toOption, hf, hw] at h
      | some ws =>
        obtain ⟨-, -, hT⟩ := erased_of h c rfl fn ws hf hw
        simp only [treeOf, shapeOf, shapeOfC, Except.toOption, hf, Option.bind_some, Option.map_some,
          treeOfFn, hw, Option.bind_eq_bind]
        exact hT

/-- A body summary: its tree `br`, the shape it was proved for and its theorem, as values (for the
generator's checks) and as names (for the generated module's kernel checks). -/
structure Summary where
  br : Br
  brName : String
  shape : List SolidCore.Solidity.Source.StorageField × FunctionDef
  shapeName : String
  minFuel : Nat
  /-- A theorem of type `SummaryOk sel minFuel shape br`. -/
  okName : String

/-- What the driver gives the generator. -/
structure Config where
  stage0 : SolarTV.MIR.Lowered.Module
  stage0Name : String
  cut : Cut
  cutName : String
  contract? : Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract
  contractName : String
  sel : Nat
  nargs : Nat
  imports : List String
  pre : String
  ns : String
  root : String
  files : Nat
  /-- The statement fuel: the source semantics' fuel the published statement names, at which the
  erasure route erases the body (`eraseLoopStmt` needs `2 ^ 256 + 1` more for a loop than for its
  body). -/
  fuel : Nat := 2 ^ 256 + 8
  /-- A summary of the function's body, checked against the imported source; `none` (the default):
  the erasure route. -/
  summary? : Option Summary := none

def refuse (why : String) : IO UInt32 := do
  IO.eprintln s!"loop obligations: refused: {why}"
  return 2

/-- The traced storage slots: every slot the template's writes, and the source tree's, read. -/
def slots : Nat := 2

/-- The source tree of the generated module and how it states it: the tree `T`, the term its
`tree` theorem equates to `some T`, the text before `tree`, and `tree`'s proof (`none`: from
`shape_eq`). -/
structure Src where
  b : Br
  T : Tree
  tree : String
  ext : String
  treeBy? : Option String

/-- The source tree from a body summary, checked against the imported function. -/
def srcOfSummary (cfg : Config) (sm : Summary) : Except String Src := do
  let some s := shapeOf cfg.contract? cfg.sel
    | throw "the checked contract has no function at the selector"
  if reprStr s.1 != reprStr sm.shape.1 then
    throw "the summary was proved for other storage fields than the imported contract's"
  if reprStr s.2 != reprStr sm.shape.2 then
    throw "the summary was proved for another function or body than the imported one"
  let some T := treeOf cfg.contract? cfg.sel sm.br
    | throw "brTree is none for the function at the selector"
  let ext := "/-- The imported contract has the summary's shape (fields, function and body), by conversion. -/\n" ++
    s!"def shapeV := Verify.LoopSource.Equiv.GenObl.shapeOf ({cfg.contractName}) {cfg.sel}\n\n" ++
    s!"kernel_rfl shape_eq shapeV (some {sm.shapeName})\n\n" ++
    "/-- **The imported function's body runs to the summary's tree.** -/\n" ++
    s!"theorem runs : Verify.LoopSource.Equiv.GenObl.Runs ({cfg.contractName}) {cfg.sel} {sm.minFuel} {sm.brName} :=\n" ++
    s!"  Verify.LoopSource.Equiv.GenObl.runs_of_summary {sm.okName} shape_eq\n\n"
  return { b := sm.br, T, ext, treeBy? := none,
           tree := s!"Verify.LoopSource.Equiv.GenObl.treeOf ({cfg.contractName}) {cfg.sel} {sm.brName}" }

/-- What `eraseLoopStmt` covers, for the refusal of a body outside it. -/
def eraseShape : String :=
  "one counted loop `for (…; i < bound; i++)` per body, whose iterations end normally or with " ++
  "Panic(0x11), add one to the words they change (the counter among them) and write only constant " ++
  "slots; no while or do-while loop, nested loop, break, continue, return, revert, log or " ++
  "condition other than `counter < bound`"

/-- The source tree from the erasure of the imported function's body at the statement fuel. -/
def srcOfErasure (cfg : Config) : Except String Src := do
  let some c := cfg.contract?.toOption
    | throw "the source does not type-check"
  let some fn := c.core.findFunctionBySelector? cfg.sel
    | throw "the checked contract has no function at the selector"
  let some ws := widthsOf fn.params fn.paramAbiCleanups
    | throw "the function's parameters are not words (widthsOf is none)"
  if fn.params.length != cfg.nargs then
    throw s!"the function has {fn.params.length} parameters, not the cut's {cfg.nargs}"
  let E : EraseEnv := { envOf c.core with facts := argFacts ws 0 }
  let some b := eraseLoopStmt E cfg.fuel fn.body (initState fn)
    | throw (if (eraseLoopStmt E (cfg.fuel + 2 ^ 257) fn.body (initState fn)).isSome then
        s!"eraseLoopStmt needs more fuel than the statement's {cfg.fuel}"
      else s!"eraseLoopStmt is none: the body is outside the erasure's shape ({eraseShape})")
  let some Te := brTree fn (argFacts ws 0) b
    | throw "brTree is none for the erased body"
  let T := loopTree Te
  -- The generated module's `kernel_rfl` recomputes exactly this.
  if (erasedOf cfg.contract? cfg.sel cfg.fuel).map (fun x => (x.1, x.2.1)) != some (cfg.nargs, b) then
    throw "erasedOf disagrees with the erasure computed here"
  let er := s!"Verify.LoopSource.Equiv.GenObl.erasedOf ({cfg.contractName}) {cfg.sel} {cfg.fuel}"
  let ext :=
    "/-- The function's body, erased by `eraseLoopStmt` at the statement fuel: the loop's closed form. -/\n" ++
    s!"def br : SolidCore.Refinement.Generic.Br := {reprStr b}\n\n" ++
    "/-- The arity, erasure and source tree of the function at the selector, as the kernel computes them by conversion. -/\n" ++
    s!"def erasedV : Option (Nat × SolidCore.Refinement.Generic.Br × SolidCore.Refinement.Generic.Tree) :=\n  {er}\n\n" ++
    "/-- The erased body's tree. -/\n" ++
    s!"def Te : SolidCore.Refinement.Generic.Tree := {reprStr Te}\n\n" ++
    s!"kernel_rfl erased_eq erasedV (some ({cfg.nargs}, br, Te))\n\n" ++
    s!"theorem erasedOf_eq : {er} = some ({cfg.nargs}, br, Te) := erased_eq\n\n" ++
    "/-- **The source premises of the join**: the imported function's arity, its body's erasure `br` and\n" ++
    "its tree `Te` (`Erased.runs` gives `BodyRuns` of it, by `bodyRuns_of_eraseLoop`). -/\n" ++
    s!"theorem erased : Verify.LoopSource.Equiv.GenObl.Erased ({cfg.contractName}) {cfg.sel} {cfg.fuel} {cfg.nargs} br Te :=\n" ++
    "  Verify.LoopSource.Equiv.GenObl.erased_of erasedOf_eq\n\n" ++
    "/-- The sequents' tree `T` is the erased tree simplified. -/\n" ++
    "theorem loop_tree : Verify.LoopSource.Equiv.GenObl.loopTree Te = T :=\n" ++
    "  Option.some.inj (treeBeq_eq (by decide +kernel))\n\n" ++
    "/-- **The erased tree and the sequents' tree observe alike on every call.** -/\n" ++
    "theorem same : ∀ ρ : SolidCore.Refinement.Generic.Val, ρ.Ok → (Te.eval ρ).obs = (T.eval ρ).obs :=\n" ++
    "  fun ρ _ => loop_tree ▸ Verify.LoopSource.Equiv.GenObl.obs_loopTree Te ρ\n\n"
  return { b, T, ext,
           treeBy? := some "by\n  rw [Verify.LoopSource.Equiv.GenObl.treeOf_of_erasedOf erasedOf_eq]\n  exact congrArg some loop_tree",
           tree := s!"(Verify.LoopSource.Equiv.GenObl.treeOf ({cfg.contractName}) {cfg.sel} br).map Verify.LoopSource.Equiv.GenObl.loopTree" }

/-- **The generator.** -/
def run (cfg : Config) : IO UInt32 := do
  let some (le, li) := cfg.cut.check .off cfg.stage0 cfg.sel cfg.nargs
    | refuse "cut.check is none: the certificate does not match the MIR"
  let r := match cfg.summary? with
    | some sm => srcOfSummary cfg sm
    | none => srcOfErasure cfg
  if let .error why := r then
    return ← refuse why
  let .ok src := r | refuse "unreachable"
  let T := src.T
  -- Header valuations only: the traced arrivals at the header.
  let vals := traceVals cfg.nargs le li (callsOf cfg.nargs slots) 20
  let I := inferT cfg.nargs cfg.cut.nhw le li vals
  let accepted := (measures cfg.nargs li).filterMap fun μ =>
    if (measureT cfg.nargs li vals).isSome && vals.all (fun σ => match leafAt σ li with
        | some (.back hs) => decide ((Inv.sub cfg.nargs hs μ).eval σ < μ.eval σ)
        | _ => true) then
      (allSeqs cfg.nargs cfg.cut.cases T le li I μ).map (μ, ·)
    else none
  let some (μ, ss) := accepted.head?
    | refuse s!"no accepted measure among {(measures cfg.nargs li).length} candidates"
  -- The source tree must be what the MIR does: a sequent with a traced counterexample refuses.
  let probe := callsOf cfg.nargs slots ++ vals
  if let some (_, i) := (ss.zipIdx.filter fun (q, _) => probe.any fun σ =>
      q.1.all (holdsB σ) && match q.2 with | some goal => !holdsB σ goal | none => true).head? then
    return ← refuse s!"the source tree disagrees with the MIR: sequent {i} has a counterexample"
  let chk := s!"{cfg.cutName}.check .off {cfg.stage0Name} {cfg.sel} {cfg.nargs}"
  let mods := emitSeqs (cfg.imports ++ ["Verify.LoopSource.Equiv.EmitSeq"])
    (["Verify.LoopSource.Equiv.GenObl"] ++ cfg.imports) cfg.pre cfg.ns "" chk src.tree cfg.nargs
    s!"{cfg.cutName}.cases" le li T I μ ss cfg.files (ext? := some src.ext) (treeBy? := src.treeBy?)
  for (stem, text) in mods do
    let f := System.FilePath.mk cfg.root / (stem ++ ".lean")
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  let rel := mods.map (·.1)
  let q (s : String) : String := "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""
  let measure := (reprStr μ).replace "\n" " "
  let route := if cfg.summary?.isSome then "summary" else "erasure"
  IO.println s!"\{\"format\":\"loop obligations 1\",\"route\":{q route},\"modules\":[{String.intercalate "," (rel.map q)}],\"measure\":{q measure}}"
  return 0

end Verify.LoopSource.Equiv.GenObl
