#!/usr/bin/env python3
r"""Lane G scaling family: N side conditions sharing the same hypotheses.

A read at q through N stores at p + 32 i (i < N), on a path where p < 2^64, p + 32 N <= q and
q < 2^64, with K unrelated path conditions besides (two per noise word pair, as the cases a
symbolic run collects). Each rewrite by Mem.read_store_disjoint raises one side condition
  q.toNat + 32 <= (Evm.add p (32 i)).toNat \/ (Evm.add p (32 i)).toNat + 32 <= q.toNat
over the same hypotheses. Writes one file per (variant, N) to OUT (default ~/g-gen/scaling):

  base      W1Proofs' sym_mem_disch_core per side condition (Model.lean's base_mem_disch)
  once      the same normalization once for all hypotheses and the goal, then omega per side
            condition
  fresh     grind only [toNat_evm_add] per side condition (no shared state)
  shared    g_simp: hypotheses internalized once, one grind state shared by all side conditions,
            the trigger toNat_evm_add instantiated by E-matching inside each attempt
  facts     g_facts first (evm_add_eq, Evm.add a b = a + b, instantiated once at every word sum
            of the goal and the hypotheses, as hypotheses), then g_simp with no trigger: no
            E-matching per side condition

usage: gen_scaling.py [OUT] [N ...]
"""
import os, sys

VARIANTS = {
    "base": "  simp (disch := base_mem_disch) only [Mem.read_store_disjoint]",
    "once": ("  simp -implicitDefEqProofs only [Evm.add, bitvec_to_nat] at *\n"
             "  simp only [Nat.reducePow, Nat.reduceMod] at *\n"
             "  simp (disch := omega) only [Mem.read_store_disjoint]"),
    "fresh": "  simp (disch := grind only [toNat_evm_add]) only [Mem.read_store_disjoint]",
    "shared": "  g_simp [Mem.read_store_disjoint] using [toNat_evm_add]\n  all_goals rfl",
    "facts": "  g_facts [evm_add_eq]\n  g_simp [Mem.read_store_disjoint]\n  all_goals rfl",
}
K = 8

def statement(n, name):
    noise_vars = " ".join(f"x{j} y{j}" for j in range(K))
    noise_hyps = "\n    ".join(f"(hn{j} : ¬Evm.add x{j} y{j} = 0) (hl{j} : x{j} < y{j})" for j in range(K))
    mem = "m"
    for i in range(n):
        mem = f"({mem}.store (Evm.add p {32 * i}).toNat v)"
    return (f"theorem {name} (m : Mem) (p q v {noise_vars} : Word)\n"
            f"    (hp : p < 18446744073709551616) (hq : Evm.add p {32 * n} ≤ q)\n"
            f"    (hq2 : q < 18446744073709551616)\n    {noise_hyps} :\n"
            f"    {mem}.read q.toNat 32 = m.read q.toNat 32 := by\n")

def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.expanduser("~/g-gen/scaling")
    ns = [int(a) for a in sys.argv[2:]] or [16, 32, 64, 128, 256]
    os.makedirs(out, exist_ok=True)
    for n in ns:
        for v, tac in VARIANTS.items():
            name = f"scale_{v}_{n}"
            with open(os.path.join(out, f"{name}.lean"), "w") as f:
                f.write("import Verify.Eval.G.Model\nimport Verify.Eval.G.Kernel\n\n")
                f.write("open Verify.Eval.G.Model\n\n")
                f.write("set_option linter.unusedVariables false\nset_option maxHeartbeats 0\n")
                f.write("set_option maxRecDepth 100000\nset_option g_simp.trace true\n\n")
                f.write(f'g_time "{v} {n}" in\n')
                f.write(statement(n, name) + tac + "\n\n")
                f.write(f"#kernel_recheck_all {name}\n#proof_stats {name}\n#print axioms {name}\n")

if __name__ == "__main__":
    main()
