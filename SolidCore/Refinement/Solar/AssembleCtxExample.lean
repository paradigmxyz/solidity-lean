import SolidCore.Refinement.Solar.AssembleCtx

/-!
# An internal function called at two stack heights: an example and mutants

\`prog\` calls the internal function at block 3 (\`x ↦ x + 1\`, returning with a dynamic jump to the
label under its argument) twice: from block 0 with one word under the call (the callee entered at
height 3) and from block 1 with two (height 4), then adds the three words and returns their sum.
\`AssembleCut.checkC\` takes one entry height and type per block and checks the callee's return
against both return labels, so no certificate of it covers the second return, which needs three
words where the first leaves two (\`single_fails\`; solar's \`asm_cert.infer\` finds no fixed point
of heights either). The checker with contexts (\`AssembleCtx.checkX\`) checks the callee once per
call site: each context knows the return label under the argument as the one its caller pushed
(\`labs\`), so the return enters the caller's own context. The certificate is
\`tools/certify/asm_cert.py\`'s \`infer_ctx\` output for this program and bytecode.

Rejected by evaluation: the bytecode whose second call returns to block 1's offset (a mutant
return label), a certificate that says the second call's return label is the first call's, and a
certificate whose second context enters the callee one word low.
-/

namespace SolidCore.Refinement.Solar.AssembleCtxExample

open SolidCore.Refinement.Solar SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCut SolidCore.Refinement.Solar.AssembleCtx
open SolidCore.Refinement.Final

def prog : Assemble.Program :=
  { blocks := [
      [.op (.stack (.push 5)), .pushLabel 1, .op (.stack (.push 7)), .jump 3],
      [.pushLabel 2, .op (.stack (.push 8)), .jump 3],
      [.op (.stack .add), .op (.stack .add), .op (.stack (.push 0)), .op .store,
        .op (.stack (.push 32)), .op (.stack (.push 0)), .ret],
      [.op (.stack (.push 1)), .op (.stack .add), .op (.stack (.swap 0)), .jumpDyn]] }

/-- PUSH1 5 PUSH1 9 PUSH1 7 PUSH1 26 JUMP; JUMPDEST PUSH1 17 PUSH1 8 PUSH1 26 JUMP; JUMPDEST ADD
ADD PUSH0 MSTORE PUSH1 32 PUSH0 RETURN; JUMPDEST PUSH1 1 ADD SWAP1 JUMP. -/
def code : ByteArray :=
  ⟨#[0x60, 0x05, 0x60, 0x09, 0x60, 0x07, 0x60, 0x1a, 0x56, 0x5b, 0x60, 0x11, 0x60, 0x08, 0x60,
    0x1a, 0x56, 0x5b, 0x01, 0x01, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3, 0x5b, 0x60, 0x01, 0x01, 0x90,
    0x56]⟩

/-- The second call's return label pushes block 1's offset (9) in place of block 2's (17). -/
def mutantRet : ByteArray :=
  ⟨#[0x60, 0x05, 0x60, 0x09, 0x60, 0x07, 0x60, 0x1a, 0x56, 0x5b, 0x60, 0x09, 0x60, 0x08, 0x60,
    0x1a, 0x56, 0x5b, 0x01, 0x01, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3, 0x5b, 0x60, 0x01, 0x01, 0x90,
    0x56]⟩

def base : Assemble.Cert :=
  { offsets := [0x0, 0x9, 0x11, 0x1a], needs := [], top := 2 ^ 140, turned := [],
    costs := [5, 5, 7, 5], rets := [1, 2] }

/-- The callee's context from the second call. -/
def calleeTwo : Ctx :=
  { need := 4, max := 4, types := [some false, some true, some false, some false],
    labs := [none, some [2]], succ := [(2, 0)], rets := [2] }

def cxWith (two : Ctx) : CtxCert :=
  { base := base,
    ctxs := [[{ need := 0, max := 0, types := [], labs := [], succ := [(3, 0)], rets := [1] }],
      [{ need := 2, max := 2, types := [some false, some false], labs := [], succ := [(3, 1)],
         rets := [2] }],
      [{ need := 3, max := 3, types := [some false, some false, some false], labs := [], succ := [],
         rets := [] }],
      [{ need := 3, max := 3, types := [some false, some true, some false], labs := [none, some [1]],
         succ := [(1, 0)], rets := [1] }, two]] }

/-- \`asm_cert.infer_ctx\`'s certificate. -/
def cx : CtxCert := cxWith calleeTwo

theorem check_ok : checkX prog code cx = true := by decide +kernel

/-- A mutant return label: the bytecode's second call returns to block 1. -/
theorem mutantRet_fails : checkX prog mutantRet cx = false := by decide +kernel

/-- The second call's return label claimed to be the first call's. -/
theorem wrongLabel_fails :
    checkX prog code (cxWith { calleeTwo with labs := [none, some [1]], rets := [1] }) = false := by
  decide +kernel

/-- The second call's context entered one word low. -/
theorem lowHeight_fails :
    checkX prog code (cxWith { calleeTwo with need := 3, max := 3, types := [some false, some true, some false] }) =
      false := by
  decide +kernel

/-- One entry per block, as \`AssembleCut.checkC\` takes it: the callee entered at three words or
more, typed as the first call leaves them; its return checks block 2's three words against the
two it knows. -/
theorem single_fails :
    checkC prog code { base with
                         needs := [0, 2, 3, 3],
                         types := [[], [some false, some false], [some false, some false, some false],
                           [some false, some true, some false]] } [0, 3, 3, 4] = false := by
  decide +kernel

/-- **The bytecode runs as the program, at every gas below \`2 ^ 256\`**:
\`AssembleCut.withinRun_of_checkC\`'s statement, from the checker with contexts. -/
theorem bytecode (scope : SolarTV.Call → Prop) :
    WithinRunLt SolarTV.evmirSem (fun _ => prog) code scope (RunOracle.CertOk cx.base) :=
  withinRun_of_checkX check_ok scope

/-- info: 'SolidCore.Refinement.Solar.AssembleCtxExample.bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecode

end SolidCore.Refinement.Solar.AssembleCtxExample
