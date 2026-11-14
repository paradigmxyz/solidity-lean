# slice-final (was erc20-certified): work before the reset

Bundles and patches of the pre-reset work, built on storm/base (not the PR heads).

- solidity-lean-wip.bundle / solidity-lean/: branch wip/slice-final-pre-reset (prerequisite 51a3270 = storm/base + sl-erc20.patch).
  AssembleCtxGas.lean (checkXL: the context checker on the loop checker's fragment with unchecked
  blocks F replaced by self-jumps; forward_of_checkXL and within_of_checkXL, no runner hypotheses,
  both compile with axioms propext/Classical.choice/Quot.sound), Verify/ShapeCtxGas.lean
  (compiled_ofXL / compiled0XL: Compiled from source stage + backend + guard stage + checkXL; not yet built),
  Verify/Spec/TreeOn.lean (allowed statuses from erased trees; not yet built), GlobLT refactor of AssembleLoop*.
- solar-wip.bundle / solar/: branch wip/slice-final-pre-reset (prerequisite 237518e9): tools/certify/asm_ctx.py,
  gen_ctx.py, gen_ctxgas.py.

Superseded by the course correction: the uv2 pieces assumed the global NestedSlotsSeparated premise and
a fixed caller; they are not to be used as is.
