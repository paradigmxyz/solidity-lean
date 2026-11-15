#!/usr/bin/env python3
"""Lane D scaling files: for each lane A fixture Verify/Eval/A/Fixtures/<Family><n>.lean, copy its
definitions (model, statement and helpers) verbatim, drop its baseline proof, and prove stmt with
Std.WP vcgen through the Loom bridge. Writes Verify/Eval/D/Scale/<Family><n>.lean, with the sha256
prefix of the copied definitions."""
import hashlib, os, re, sys

root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
src_dir = os.path.join(root, "Verify/Eval/A/Fixtures")
out_dir = os.path.join(root, "Verify/Eval/D/Scale")
os.makedirs(out_dir, exist_ok=True)

WP = "  unfold stmt\n  intro s herr\n  intros\n  refine loom_wp_of_triple_pt ?_\n  vcgen [model] with finish\n"
PROOF = {
  "Straight": WP, "Branch": WP, "Memory": WP, "Shared": WP,
  "LoopBody": "  unfold stmt\n  intro N s i hi herr s' hinv\n  refine loom_wp_of_triple_pt ?_\n  simp only [inv] at hinv\n  vcgen [body] <;> simp [inv, variant, LE.pure, ite_apply] at * <;> grind\n",
}
only = sys.argv[1:]
for fn in sorted(os.listdir(src_dir)):
    m = re.fullmatch(r"([A-Za-z]+?)(\d+)\.lean", fn)
    if not m: continue
    fam, n = m.group(1), m.group(2)
    if fam not in PROOF or (only and fam + n not in only): continue
    text = open(os.path.join(src_dir, fn)).read()
    ns = re.search(r"^namespace (\S+)", text, re.M).group(1)
    body = text[text.index("namespace " + ns) + len("namespace " + ns):text.index("end " + ns)]
    b = body.index("theorem baseline")
    rest = body[b:]
    nxt = re.search(r"\n(def |abbrev |theorem |/--|@\[)", rest[1:])
    defs = body[:b] + (rest[1 + nxt.start():] if nxt else "")
    h = hashlib.sha256(defs.strip().encode()).hexdigest()[:16]
    out = (
        "import Verify.Eval.D.Bridge\nimport Verify.Eval.Common.Measure\n\n"
        f"/-! Lane D on lane A's fixture {fam}{n}: the definitions of Verify/Eval/A/Fixtures/{fn} copied\n"
        f"verbatim by scripts/eval/gen_d_scale.py (sha256 prefix {h}), stmt proved with vcgen. -/\n\n"
        "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option experimental.vcgen true\n"
        "set_option grind.warning false\nset_option Elab.async false\n\n"
        f"namespace Verify.Eval.D.Scale.{fam}{n}\n\n"
        "open SolidCore.Verify SolidCore.Verify.Eval.D\nopen scoped Std.WP\n\n"
        f"{defs.strip()}\n\n#timed theorem vcgen_new : stmt := by\n{PROOF[fam]}\n"
        f"end Verify.Eval.D.Scale.{fam}{n}\n\n"
        f"#print axioms Verify.Eval.D.Scale.{fam}{n}.vcgen_new\n"
        f"#proof_stats Verify.Eval.D.Scale.{fam}{n}.vcgen_new\n"
        f"#kernel_recheck Verify.Eval.D.Scale.{fam}{n}.vcgen_new\n")
    open(os.path.join(out_dir, f"{fam}{n}.lean"), "w").write(out)
    print(fam, n, h)
