# rebase lane: work in progress before the reset

`rebase-wip.bundle` (solar) holds two branches:

- `wip/rebase-main-into-lean` (a5eb41c49): feat/lean-solar e5320bb8 with main 05d39ec29 merged
  and the translation-validation model ported to main's `extcall` (one call primitive): MIR
  semantics, mir-interpreter, solar-tv-replay export, solar-tv importer and Lean
  (`MessageOp.extcall`), tests and examples moved to the `extcall` syntax.
- `wip/rebase-pre-reset` (628d43434): that merge with storm/solar-sq merged on top.

Prerequisites: feat/lean-solar e5320bb8, main 05d39ec29, and storm/solar-sq 237518e9 (in
`storm/solar-storm.bundle`). Superseded by the merge onto alpharush/certified 38b5232 in
`storm/out/rebase/`.
