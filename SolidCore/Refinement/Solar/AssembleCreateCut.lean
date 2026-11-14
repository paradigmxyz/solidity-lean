import SolidCore.Refinement.Solar.AssembleCut
import SolidCore.Refinement.Solar.AssembleCreateSegOracle

/-!
# CALL, CREATE2 and CODECOPY at a cut of the checker

The checker cuts a block at CALL, CREATE2 and CODECOPY (`AssembleCutSim.blockOkC`, under a
certificate that says the program creates). These are the facts a segment proof takes at such a cut:
the code the lowering lays out there (one opcode each), and SolarTV's run of the rest of the block from
the effect's result, which the cut lemmas (`AssembleCallValueSeg.callValue_cut`,
`AssembleCallValueZeroSeg.call0_cut`, `AssembleCreateSeg.create2_cut`,
`AssembleCreateSeg.codecopy_cut`) give under the oracle of the run's tables.
-/

namespace SolidCore.Refinement.Solar.AssembleCreateCut

open SolarTV SolarTV.Machine
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCut
open SolarTV.EVM.Program

theorem lowerInstrs_call (p : Assemble.Program) (c : Cert) (b : Nat) (rest : List Assemble.Instr) :
    lowerInstrs p c b (.effect (.call .call) 7 :: rest) = .op 0xf1 :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr]

theorem lowerInstrs_c2 (p : Assemble.Program) (c : Cert) (b : Nat) (rest : List Assemble.Instr) :
    lowerInstrs p c b (.effect .create2 4 :: rest) = .op 0xf5 :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr]

theorem lowerInstrs_cc (p : Assemble.Program) (c : Cert) (b : Nat) (rest : List Assemble.Instr) :
    lowerInstrs p c b (.effect .codecopy 3 :: rest) = .op 0x39 :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr]

/-- SolarTV's run of a block from a CALL: the rest of the block from the call's flag. -/
theorem exec_callC {o : Oracle} {call : Call} {b : Nat} {rest : List Assemble.Instr}
    {a1 a2 a3 a4 a5 a6 a7 w : Word} {S : List Word} {s s2 : State}
    (happ : Effect.apply o call (.call .call) [a1, a2, a3, a4, a5, a6, a7] s = some (some w, s2))
    (h : S.length < 1024) :
    exec o call b (.effect (.call .call) 7 :: rest) (a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: S) s =
      exec o call b rest (w :: S) s2 := by
  simp [exec, happ, show ¬ 1024 < S.length + 1 by omega]

/-- SolarTV's run of a block from a CREATE2: the rest of the block from the word it pushes. -/
theorem exec_c2C {o : Oracle} {call : Call} {b : Nat} {rest : List Assemble.Instr}
    {a1 a2 a3 a4 w : Word} {S : List Word} {s s2 : State}
    (happ : Effect.apply o call .create2 [a1, a2, a3, a4] s = some (some w, s2))
    (h : S.length < 1024) :
    exec o call b (.effect .create2 4 :: rest) (a1 :: a2 :: a3 :: a4 :: S) s =
      exec o call b rest (w :: S) s2 := by
  simp [exec, happ, show ¬ 1024 < S.length + 1 by omega]

/-- SolarTV's run of a block from a CODECOPY: the rest of the block from the copy. -/
theorem exec_ccC {o : Oracle} {call : Call} {b : Nat} {rest : List Assemble.Instr}
    {d off sz : Word} {S : List Word} {s s2 : State}
    (happ : Effect.apply o call .codecopy [d, off, sz] s = some (none, s2)) (h : S.length ≤ 1024) :
    exec o call b (.effect .codecopy 3 :: rest) (d :: off :: sz :: S) s = exec o call b rest S s2 := by
  simp [exec, happ, show ¬ 1024 < S.length by omega]

/-- **A CODECOPY cut, read back**: SolarTV's run of the block from the CODECOPY is the run of the rest
from SolarTV's copy, which `AssembleCreateSeg.codecopy_cut` relates to EthLib's under an oracle that
reads the frame's code, at a code offset the checker knows below 2 ^ 32
(`AssembleCut.blockOkC_cc`). -/
theorem exec_codecopy {o : Oracle} {call : Call} {b : Nat} {rest : List Assemble.Instr}
    {d off sz : Word} {S : List Word} {s : State}
    (h : S.length ≤ 1024) :
    exec o call b (.effect .codecopy 3 :: rest) (d :: off :: sz :: S) s =
      exec o call b rest S (AssembleCreateSeg.codeCopied o s d off sz) :=
  exec_ccC (AssembleCodeCopy.codecopy_effect o call d off sz s) h

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateCut.exec_codecopy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exec_codecopy

end SolidCore.Refinement.Solar.AssembleCreateCut
