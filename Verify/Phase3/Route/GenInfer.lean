import Verify.LoopSource.Equiv.GenObl
import Verify.Phase3.Infer.SeqW

/-!
# The erasure route with a discovered invariant (untrusted generator)

`GenObl.run` infers a loop's invariant from traced header valuations (`Inv.cands`) and states the
sequents with `Inv.allSeqs`. When no candidate set and measure give sequents (no accepted measure,
or `allSeqs` is `none` because an end returns a computed word), the driver asks
`tools/certify/loop_infer.py` for an invariant and a measure. This module is that route's two
generator steps, on the same `GenObl.Config` the driver writes for `GenObl.run`:

* `exportLeaves cfg path`: the leaves of the cut-point check and **the tree of the source's own erasure**
  (`GenObl.srcOfErasure`: `eraseLoopStmt` of the imported function's body at the statement fuel,
  then `loopTree`), as the JSON `loop_infer.py` reads (`"tree_source": "erasure"`). The tool's
  property is this tree, not a target it is handed: the obligations it proposes an invariant for
  are the ones `GeneratedTarget` / `Route.final_of_generatedW` take, whose tree is the erased one.
* `emit cfg I μ`: with the tool's invariant `I` and measure `μ`, the sequents `allSeqsW` (which
  also compares ends that return words), refused when a traced call refutes one; then the same
  modules `GenObl.run` writes (Data, V0..Vk, Obl with the erasure's `erased_eq`, `erased`,
  `loop_tree` and `same`), with `seqs` over `allSeqsW` and `obl` by `obl_of_seqsW`. It prints
  `GenObl.run`'s JSON line with `"route": "erasure-inferred"`.

Nothing here is trusted: the kernel checks every fact the modules state when they are built.
-/

namespace Verify.Phase3.Route.GenInfer
open SolidCore.Refinement.Generic Verify.LoopSource.Equiv Verify.LoopSource.Equiv.Inv
open Verify.LoopSource.Equiv.GenObl

/-! ## JSON, as `loop_infer.py` reads it -/

def q (s : String) : String := "\"" ++ s ++ "\""

def binS : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .lt => "lt" | .gt => "gt"
  | .eq => "eq" | .and => "and" | .or => "or" | .xor => "xor" | .shl => "shl" | .shr => "shr"
  | .byte => "byte"

def unS : UnOp → String
  | .iszero => "iszero" | .not => "not"

def wj : WExpr → String
  | .lit n => s!"[\"lit\",{n}]"
  | .arg i => s!"[\"arg\",{i}]"
  | .init k => s!"[\"init\",{k}]"
  | .un op a => s!"[\"un\",{q (unS op)},{wj a}]"
  | .bin op a b => s!"[\"bin\",{q (binS op)},{wj a},{wj b}]"
  | .sinit k => s!"[\"sinit\",{wj k}]"
  | .sel c a b => s!"[\"sel\",{wj c},{wj a},{wj b}]"
  | .hash a b => s!"[\"hash\",{wj a},{wj b}]"
  | .caller => "[\"caller\"]"

def arr (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

def bj : OByte → String
  | .lit b => s!"[\"blit\",{b}]"
  | .byteOf e i => s!"[\"byteOf\",{wj e},{i}]"

def tj : Tree → String
  | .halt ok out ws ls =>
    s!"[\"halt\",{ok},{arr (out.map bj)},{arr (ws.map fun w => arr [wj w.1, wj w.2])},{ls.length}]"
  | .ite c t e => s!"[\"ite\",{wj c},{tj t},{tj e}]"

def kj (K : Facts) : String := arr (K.map fun p => arr [wj p.1, toString p.2])

def oj : Out → String
  | .exit T => s!"[\"exit\",{tj T}]"
  | .back hs => s!"[\"back\",{arr (hs.map wj)}]"

def lj (ls : List (Facts × Out)) : String := arr (ls.map fun p => arr [kj p.1, oj p.2])

/-! ## The two steps -/

/-- **Export** the cut check's leaves and the erased tree for `loop_infer.py`. -/
def exportLeaves (cfg : Config) (path : String) : IO UInt32 := do
  let some (le, li) := cfg.cut.check .off cfg.stage0 cfg.sel cfg.nargs
    | refuse "cut.check is none: the certificate does not match the MIR"
  match srcOfErasure cfg with
  | .error why => refuse why
  | .ok src =>
    let j := s!"\{\"format\":\"loop leaves 1\",\"tree_source\":\"erasure\",\"sel\":{cfg.sel},\"n\":{cfg.nargs},\"nhw\":{cfg.cut.nhw},\"cases\":{arr (cfg.cut.cases.map kj)},\"le\":{lj le},\"li\":{lj li},\"T\":{tj src.T}}"
    IO.FS.writeFile path (j ++ "\n")
    IO.println s!"\{\"format\":\"loop leaves export 1\",\"path\":{q path},\"le\":{le.length},\"li\":{li.length}}"
    return 0

/-- Replace the one occurrence of `a` in `s` by `b`; `none` when `a` does not occur exactly once. -/
def replaceOnce (s a b : String) : Option String :=
  match s.splitOn a with
  | [x, y] => some (x ++ b ++ y)
  | _ => none

/-- **Emit** the obligation modules for the tool's invariant `I` and measure `μ`. -/
def emit (cfg : Config) (I : List F) (μ : WExpr) : IO UInt32 := do
  let some (le, li) := cfg.cut.check .off cfg.stage0 cfg.sel cfg.nargs
    | refuse "cut.check is none: the certificate does not match the MIR"
  let src ← match srcOfErasure cfg with
    | .error why => do let _ ← refuse why; return 2
    | .ok src => pure src
  let T := src.T
  let some ss := Verify.Phase3.Infer.allSeqsW cfg.nargs cfg.cut.cases T le li I μ
    | refuse "allSeqsW is none for the proposed invariant and measure"
  -- A traced call that refutes a sequent refuses the candidate (the kernel would too).
  let vals := traceVals cfg.nargs le li (callsOf cfg.nargs slots) 20
  let probe := callsOf cfg.nargs slots ++ vals
  if let some (_, i) := (ss.zipIdx.filter fun (s, _) => probe.any fun σ =>
      s.1.all (holdsB σ) && match s.2 with | some goal => !holdsB σ goal | none => true).head? then
    return ← refuse s!"sequent {i} of the proposed invariant has a traced counterexample"
  let chk := s!"{cfg.cutName}.check .off {cfg.stage0Name} {cfg.sel} {cfg.nargs}"
  let mods := emitSeqs (cfg.imports ++ ["Verify.LoopSource.Equiv.EmitSeq", "Verify.Phase3.Infer.SeqW"])
    (["Verify.LoopSource.Equiv.GenObl", "Verify.Phase3.Infer.SeqW"] ++ cfg.imports) cfg.pre cfg.ns "" chk
    src.tree cfg.nargs s!"{cfg.cutName}.cases" le li T I μ ss cfg.files (ext? := some src.ext)
    (treeBy? := src.treeBy?)
  -- `emitSeqs` states `allSeqs`; this route's sequents are `allSeqsW`'s.
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
  IO.println s!"\{\"format\":\"loop obligations 1\",\"route\":\"erasure-inferred\",\"modules\":[{String.intercalate "," (rel.map qq)}],\"measure\":{qq measure},\"sequents\":{ss.length}}"
  return 0

end Verify.Phase3.Route.GenInfer
