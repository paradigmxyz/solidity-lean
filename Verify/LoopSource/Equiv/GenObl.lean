import Verify.LoopSource.Equiv.EmitSeq
import Verify.LoopSource.Equiv.Emit
import SolidCore.Refinement.Generic.SourceCall
import SolidCore.Refinement.Generic.LoopRun

/-!
# The loop-obligation generator the certify driver runs (untrusted)

`run cfg` writes, under `cfg.root`, the modules `<pre>Data`, `<pre>V0`..`<pre>Vk` and `<pre>Obl`
for one loop-carrying function: the leaves of its cut-point check, the source tree, the inferred
invariant and measure, the sequents and their `wordnorm` proofs, and the theorems `leaves`,
`tree`, `seqs`, `valid` and `obl` in `cfg.ns`. Nothing here is trusted: every fact the modules
state is checked by the kernel when they are built.

The source tree is `brTree fn (argFacts ws 0) b` for the function `fn` at `cfg.sel` in the checked
contract and the body summary's tree `b` (`cfg.summary?`): the source erasure has no case for a loop,
so the loop route's summary must be given, and it is checked against the imported source. The
generator refuses when the summary's shape (fields, function, body) is not the imported contract's,
or a sequent has a traced counterexample; the generated module proves `shape_eq` and `runs`.

It prints one JSON line `{"format":"loop obligations 1","modules":[…],"measure":"…"}` (module stems
relative to `cfg.root`) and returns 0, or returns 2 with the reason on stderr when the cut-point
check, the source tree or the sequents are none, or no measure is accepted.
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
  intro c hc fn ws hf hw fuel hfu
  subst hc
  have hs' : shapeOfC c sel = some s := hs
  have : s = (c.core.storageFields, fn) := by
    simp only [shapeOfC, hf, Option.map_some, Option.some.injEq] at hs'; exact hs'.symm
  subst this
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
  /-- The loop route's summary of the function's body. `none`: refuse. -/
  summary? : Option Summary := none

def refuse (why : String) : IO UInt32 := do
  IO.eprintln s!"loop obligations: refused: {why}"
  return 2

/-- The traced storage slots: every slot the template's writes, and the source tree's, read. -/
def slots : Nat := 2

/-- **The generator.** -/
def run (cfg : Config) : IO UInt32 := do
  let some sm := cfg.summary?
    | refuse "no body summary (summary? is none): the source erasure has no loop case"
  let some s := shapeOf cfg.contract? cfg.sel
    | refuse "the checked contract has no function at the selector"
  if reprStr s.1 != reprStr sm.shape.1 then
    return ← refuse "the summary was proved for other storage fields than the imported contract's"
  if reprStr s.2 != reprStr sm.shape.2 then
    return ← refuse "the summary was proved for another function or body than the imported one"
  let b := sm.br
  let some (le, li) := cfg.cut.check .off cfg.stage0 cfg.sel cfg.nargs
    | refuse "cut.check is none: the certificate does not match the MIR"
  let some T := treeOf cfg.contract? cfg.sel b
    | refuse "brTree is none for the function at the selector"
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
  -- The summary's tree must be what the MIR does: a sequent with a traced counterexample refuses.
  let probe := callsOf cfg.nargs slots ++ vals
  if let some (_, i) := (ss.zipIdx.filter fun (q, _) => probe.any fun σ =>
      q.1.all (holdsB σ) && match q.2 with | some goal => !holdsB σ goal | none => true).head? then
    return ← refuse s!"the summary's tree disagrees with the MIR: sequent {i} has a counterexample"
  let chk := s!"{cfg.cutName}.check .off {cfg.stage0Name} {cfg.sel} {cfg.nargs}"
  let tree := s!"Verify.LoopSource.Equiv.GenObl.treeOf ({cfg.contractName}) {cfg.sel} {sm.brName}"
  let ext := "/-- The imported contract has the summary's shape (fields, function and body), by conversion. -/\n" ++
    s!"def shapeV := Verify.LoopSource.Equiv.GenObl.shapeOf ({cfg.contractName}) {cfg.sel}\n\n" ++
    s!"kernel_rfl shape_eq shapeV (some {sm.shapeName})\n\n" ++
    "/-- **The imported function's body runs to the summary's tree.** -/\n" ++
    s!"theorem runs : Verify.LoopSource.Equiv.GenObl.Runs ({cfg.contractName}) {cfg.sel} {sm.minFuel} {sm.brName} :=\n" ++
    s!"  Verify.LoopSource.Equiv.GenObl.runs_of_summary {sm.okName} shape_eq\n\n"
  let mods := emitSeqs (cfg.imports ++ ["Verify.LoopSource.Equiv.EmitSeq"])
    (["Verify.LoopSource.Equiv.GenObl"] ++ cfg.imports) cfg.pre cfg.ns "" chk tree cfg.nargs
    s!"{cfg.cutName}.cases" le li T I μ ss cfg.files (ext? := some ext)
  for (stem, text) in mods do
    let f := System.FilePath.mk cfg.root / (stem ++ ".lean")
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f text
  let rel := mods.map (·.1)
  let q (s : String) : String := "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""
  let measure := (reprStr μ).replace "\n" " "
  IO.println s!"\{\"format\":\"loop obligations 1\",\"modules\":[{String.intercalate "," (rel.map q)}],\"measure\":{q measure}}"
  return 0

end Verify.LoopSource.Equiv.GenObl
