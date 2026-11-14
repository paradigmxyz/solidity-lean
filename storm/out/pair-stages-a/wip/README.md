# pair-stages-a: work before the reset

- solar-wip.bundle: branch wip/pair-stages-a-pre-reset (794fc28b7) on storm/solar-sq (237518e9).
  certify.py/cutpoints.py: cut-point (loop) stages scoped to kept functions (--exclude no
  longer turns cut points off). Checked: callsqrt with g excluded builds all stages and
  Execution (cs_scope_bytecode at scope), axioms propext/Classical.choice/Quot.sound.
- sl-wip.bundle: branch wip/pair-stages-a-pre-reset on storm/base (d54dabf): lakefile entries
  for the scoped libraries only (the Pair stages are generated, not committed).
- Not reached: the Pair's MIR stage segments (stage0 -> mir1) time out at whnf under 2e6
  heartbeats with mint/burn kept (21 segments, fuel 14508, about 5 GB).
