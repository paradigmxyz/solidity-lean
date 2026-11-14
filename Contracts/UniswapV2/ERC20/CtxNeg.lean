import uv2_erc20.Ctx
import W1Proofs.Axioms

/-!
# Negative controls of UniswapV2ERC20's context-checker certificate

The checker refuses the exact bytecode with one byte changed, by the kernel's evaluation: a jump
target moved (byte 7, the dispatcher's guard `PUSH1 0x65`), the first SSTORE dropped (as POP,
byte 685) and an opcode outside the fragment (CREATE) for that SSTORE. Each refusal is a mismatch
of the walk against the final EVM IR, never a timeout.
-/

namespace SolarTV.Export.UniswapV2ERC20.Ctx

open SolidCore.Refinement.Solar SolidCore.Refinement.Solar.AssembleCtx

/-- The bytecode with byte `i` replaced by `b`. -/
noncomputable def mutant (i b : Nat) : ByteArray := ⟨((bytes.set i b).map UInt8.ofNat).toArray⟩

theorem rejects_jump : checkXB (norm evm16) (mutant 7 0x66) cx = false := by decide +kernel

theorem rejects_sstore : checkXB (norm evm16) (mutant 685 0x50) cx = false := by decide +kernel

theorem rejects_opcode : checkXB (norm evm16) (mutant 685 0xf0) cx = false := by decide +kernel

/-- info: 'SolarTV.Export.UniswapV2ERC20.Ctx.rejects_sstore' depends on axioms within [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#axioms_within rejects_sstore

end SolarTV.Export.UniswapV2ERC20.Ctx
