import Verify.LoopSource.Equiv.EmitSeq
import Verify.LoopSource.Equiv.Emit
import SolidCore.Refinement.Generic.SourceCall

/-!
# The loop-obligation generator the certify driver runs (untrusted)

\`run cfg\` writes, under \`cfg.root\`, the modules \`<pre>Data\`, \`<pre>V0\`..\`<pre>Vk\` and \`<pre>Obl\`
for one loop-carrying function: the leaves of its cut-point check, the source tree, the inferred
invariant and measure, the sequents and their \`wordnorm\` proofs, and the theorems \`leaves\`,
\`tree\`, \`seqs\`, \`valid\` and \`obl\` in \`cfg.ns\`. Nothing here is trusted: every fact the modules
state is checked by the kernel when they are built.

The source tree is \`brTree fn (argFacts ws 0) b\` for the function \`fn\` at \`cfg.sel\` in the checked
contract and the body summary \`b\` (\`cfg.body?\`): the source erasure has no case for a loop, so the
loop route's summary of the function's body must be given. Without it \`run\` refuses.

It prints one JSON line \`{"format":"loop obligations 1","modules":[…],"measure":"…"}\` (module stems
relative to \`cfg.root\`) and returns 0, or returns 2 with the reason on stderr when the cut-point
check, the source tree or the sequents are none, or no measure is accepted.
-/

namespace Verify.LoopSource.Equiv.GenObl
open SolidCore.Refinement.Generic Verify.LoopSource.Equiv Verify.LoopSource.Equiv.Inv

/-- The source tree of the function at \`sel\` of a checked contract, from its body summary \`b\`. -/
def treeOf (c? : Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract)
    (sel : Nat) (b : Br) : Option Tree := do
  let c ← c?.toOption
  let fn ← c.core.findFunctionBySelector? sel
  let ws ← widthsOf fn.params fn.paramAbiCleanups
  brTree fn (argFacts ws 0) b

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
  /-- The loop route's summary of the function's body, and its name. \`none\`: refuse. -/
  body? : Option Br := none
  bodyName : String := ""

def refuse (why : String) : IO UInt32 := do
  IO.eprintln s!"loop obligations: refused: {why}"
  return 2

/-- The traced storage slots: every slot the template's writes, and the source tree's, read. -/
def slots : Nat := 2

/-- **The generator.** -/
def run (cfg : Config) : IO UInt32 := do
  let some (le, li) := cfg.cut.check .off cfg.stage0 cfg.sel cfg.nargs
    | refuse "cut.check is none: the certificate does not match the MIR"
  let some b := cfg.body?
    | refuse "no body summary (body? is none): the source erasure has no loop case"
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
  let chk := s!"{cfg.cutName}.check .off {cfg.stage0Name} {cfg.sel} {cfg.nargs}"
  let tree := s!"Verify.LoopSource.Equiv.GenObl.treeOf ({cfg.contractName}) {cfg.sel} {cfg.bodyName}"
  let mods := emitSeqs (cfg.imports ++ ["Verify.LoopSource.Equiv.EmitSeq"])
    (["Verify.LoopSource.Equiv.GenObl"] ++ cfg.imports) cfg.pre cfg.ns "" chk tree cfg.nargs
    s!"{cfg.cutName}.cases" le li T I μ ss cfg.files
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
