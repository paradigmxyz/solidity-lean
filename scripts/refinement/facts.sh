#!/usr/bin/env bash
# Check solar's dataflow facts on the refinement corpus in Lean.
#
#   scripts/refinement/facts.sh           rewrite SolidCore/Refinement/Facts/*.lean
#   scripts/refinement/facts.sh --check   the same, then fail if any generated file changed
#
# solar records, with -Zprove-analyses, every fact an optimization relied on (an
# SCCP constant, a check that check elimination dropped, a read that CSE or load
# PRE forwarded, an induction variable bound) at the end of a MIR block, and
# writes each as an SMT-LIB query whose assertions are contradictory exactly when
# the fact holds on every execution the query encodes. tools/prove-analyses runs
# Z3 on the queries and, with --certify-lean, translates each proved one with
# crates/smt/src/certify/lean.rs into a Lean theorem that the query's assertions
# imply False, proved by bv_decide, and checks it with Lean.
#
# This script builds solar and tools/prove-analyses at the commit in
# scripts/refinement/prove-rev into PROVE_DIR (default .cache/solar-prove), or
# takes both binaries from the directory PROVE_TARGET, runs them over every
# scripts/refinement/corpus/*.sol at -O gas (solar's default, which gen.sh
# compiles with), and collects the translator's theorems, unchanged but for
# their names and the preamble they share, into
#   SolidCore/Refinement/Facts/NAME.lean     one module per corpus contract
#   SolidCore/Refinement/Facts/Prelude.lean  the translator's store function
#   SolidCore/Refinement/Facts.lean          the root importing them
# A fact Z3 or Lean did not prove gets a comment with the reason instead of a
# theorem. Z3 comes from its pinned release, checked against its SHA-256, unless
# Z3 names a binary; Lean is the repository's toolchain.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."

check=0
[[ "${1-}" == "--check" ]] && check=1

rev="$(tr -d '[:space:]' < scripts/refinement/prove-rev)"
prove_dir="${PROVE_DIR:-.cache/solar-prove}"

if [[ -z "${PROVE_TARGET-}" ]]; then
  if [[ ! -d "$prove_dir/.git" ]]; then
    git init -q "$prove_dir"
    git -C "$prove_dir" remote add origin https://github.com/paradigmxyz/solar.git
  fi
  git -C "$prove_dir" fetch -q --depth 1 origin "$rev"
  git -C "$prove_dir" checkout -q --detach "$rev"
  cargo build --release --locked --manifest-path "$prove_dir/Cargo.toml" \
    -p solar-compiler --bin solar
  cargo build --release --locked --manifest-path "$prove_dir/Cargo.toml" \
    -p solar-prove-analyses
  PROVE_TARGET="$prove_dir/target/release"
fi
solar="$PROVE_TARGET/solar"
prover="$PROVE_TARGET/solar-prove-analyses"

version="$("$solar" --version | head -n 1)"
if [[ "$version" != *"${rev:0:8}"* ]]; then
  echo "error: $solar reports '$version', not commit $rev" >&2
  exit 1
fi

z3_version=4.15.4
z3_sha256=a41b690e89c343931471506cdc6d957b6044a200fd2d240cc017432afdff7d3e
if [[ -z "${Z3-}" ]]; then
  Z3=".cache/z3-$z3_version-x64-glibc-2.39/bin/z3"
  if [[ ! -x "$Z3" ]]; then
    mkdir -p .cache
    curl -fsSL -o .cache/z3.zip.tmp \
      "https://github.com/Z3Prover/z3/releases/download/z3-$z3_version/z3-$z3_version-x64-glibc-2.39.zip"
    echo "$z3_sha256  .cache/z3.zip.tmp" | sha256sum -c --quiet
    (cd .cache && unzip -q -o z3.zip.tmp && rm z3.zip.tmp)
  fi
fi

# Z3's limits are resource counts, so its verdicts do not depend on machine load.
# The limit and memory for a query proved alone are above the tool's defaults,
# which c6's loop needs.
# The compiler runs in each source's directory, so the paths it gets are absolute.
run="$(realpath -m "${FACTS_RUN_DIR:-.cache/facts-run}")"
rm -rf "$run"
"$prover" --solar "$solar" --z3 "$Z3" --levels gas \
  --rlimit 400000000 --memory 8000 --timeout 300 --jobs "${FACTS_JOBS:-2}" \
  --certify-lean --lean "$(command -v lean)" --lean-project "$PWD" --certify-timeout 600 \
  --out "$run" scripts/refinement/corpus >&2

out=SolidCore/Refinement/Facts
rm -rf "$out"
mkdir -p "$out"
python3 - "$run/results.jsonl" "$out" "$rev" "$version" <<'EOF'
import json, os, re, sys, textwrap

results, out, rev, version = sys.argv[1:]
# What the translator writes before each theorem.
STORE = """def store {a b : Nat} (m : BitVec a → BitVec b) (i : BitVec a) (v : BitVec b) :
    BitVec a → BitVec b :=
  fun j => if j = i then v else m j
"""
OPTIONS = """set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
"""
PREAMBLE = "import Std.Tactic.BVDecide\n\n" + STORE + "\n" + OPTIONS + "\n"
KINDS = {
    "sccp": "a constant SCCP substituted for a value",
    "check_elim": "a branch, check, overflow test or equality that check elimination decided",
    "cse": "a memory, storage or transient read CSE forwarded from an earlier value",
    "load_pre": "a read load PRE forwarded from the values reaching it",
    "indvar_simplify": "the entry bound induction variable simplification relied on",
}
QUERY = re.compile(
    r"^(?P<module>.+)-f(?P<fid>\d+)-bb(?P<bb>\d+)-(?P<lhs>[^-]+)-(?P<kind>[a-z_]+)-(?P<index>\d+)\.smt2$"
)

records = [json.loads(line) for line in open(results)]
if not records:
    sys.exit("error: the prover recorded no facts; did the compiles fail?")
corpus = sorted(
    (f for f in os.listdir("scripts/refinement/corpus") if f.endswith(".sol")),
    key=lambda f: (len(f), f),
)
by_source = {name: [] for name in corpus}
for r in records:
    by_source[os.path.basename(r["source"])].append(r)


def parts(r):
    return QUERY.match(os.path.basename(r["query"]))


def comment(text, prefix):
    text = text.replace("-/", "- /").replace("/-", "/ -")
    return textwrap.fill(prefix + text, width=100, break_long_words=False, break_on_hyphens=False)


modules = []
for name in corpus:
    module = name[0].upper() + name[1:-4]
    modules.append(module)
    facts = sorted(by_source[name], key=lambda r: (int(parts(r)["fid"]), int(parts(r)["index"])))
    proved = [r for r in facts if r["result"] == "unsat"]
    checked = [r for r in facts if r.get("certificate") == "checked-lean"]
    kinds = sorted({parts(r)["kind"] for r in facts})
    lines = [
        "-- Generated by scripts/refinement/facts.sh. Do not edit.",
        f"-- Source: scripts/refinement/corpus/{name}",
        f"-- solar: {version}",
        f"-- solar commit: {rev}",
        "",
        "import SolidCore.Refinement.Facts.Prelude",
        "",
        "/-!",
        f"# solar's analysis facts for `{name}`",
        "",
        "Each theorem is the Lean translation, by solar's `crates/smt/src/certify/lean.rs`, of the",
        "query `-Zprove-analyses` writes for one fact an optimization relied on in contract",
        "`Main`, compiled at `-O gas`: the definitions of the values in the blocks that",
        "dominate the fact's program point, with EVM word semantics, the branch conditions into",
        "them and the facts checked before it, together with the fact's negation, imply `False`.",
        "They are facts about solar's MIR at `lower-assumes`, not about the runtime bytecode.",
        "",
        f"Facts recorded: {len(facts)}. Proved by Z3: {len(proved)}. Checked in Lean by the prover and",
        f"emitted here: {len(checked)}.",
        "",
        "Fact kinds in this module:",
    ]
    for kind in kinds:
        lines.append(f"- `{kind}`: {KINDS.get(kind, kind)}.")
    if not kinds:
        lines.append("- none: no optimization of this contract relied on a recorded fact.")
    lines += ["-/", "", OPTIONS, f"namespace SolidCore.Refinement.Facts.{module}", ""]
    for r in facts:
        q = os.path.basename(r["query"])
        m = parts(r)
        function = r.get("function", "")
        fname = re.sub(r"[^A-Za-z0-9_]", "_", function.split(" ", 1)[-1])
        ident = f"f{m['fid']}_{fname}_bb{m['bb']}_{m['lhs']}_{m['kind']}_{m['index']}"
        about = [
            f"Contract `Main`, function `{function}`, fact {m['index']}:",
            f"`{r.get('claim', '')}`, its left operand defined by `{r.get('definition', '')}`.",
            f"Query `{q}`.",
        ]
        if r.get("axioms"):
            about.append(f"The query assumes the backend axioms `{r['axioms']}`.")
        if r.get("opaque"):
            about.append(f"Its goal depends on the unconstrained values `{r['opaque']}`.")
        if r.get("certificate") != "checked-lean":
            reason = r["result"]
            if r.get("counterexample"):
                reason += f", Z3 model {r['counterexample']}"
            for field in ("certificate", "lean_certificate"):
                if r.get(field):
                    reason += f", {r[field]}"
            about.append(f"Not proved: {reason}.")
            lines.append(comment(" ".join(about), f"/- Not emitted: {ident}. ") + " -/")
            lines.append("")
            continue
        tier = r.get("certified_tier", "exact")
        if tier == "abstract":
            about.append(
                "Certified in the query's abstract tier, which replaces non-constant "
                "multiplication, division and remainder by functions obeying their laws, "
                "so it implies the exact query."
            )
        stem = r["query"][: -len(".smt2")]
        lean = open(stem + (".abstract" if tier == "abstract" else "") + ".lean").read()
        if not lean.startswith(PREAMBLE):
            sys.exit(f"error: {stem}.lean: unexpected preamble from the translator")
        body, _, tail = lean[len(PREAMBLE):].partition("\n#print axioms query\n")
        if tail.strip() or not body.startswith("theorem query "):
            sys.exit(f"error: {stem}.lean: unexpected theorem from the translator")
        lines.append(comment(" ".join(about), "/-- ") + " -/")
        lines.append("theorem " + ident + body[len("theorem query"):].rstrip("\n"))
        lines.append("")
    lines += [f"end SolidCore.Refinement.Facts.{module}", ""]
    with open(f"{out}/{module}.lean", "w") as f:
        f.write("\n".join(lines))
    print(
        f"scripts/refinement/corpus/{name}: {len(facts)} facts, {len(proved)} proved, "
        f"{len(checked)} emitted -> {out}/{module}.lean"
    )

with open(f"{out}/Prelude.lean", "w") as f:
    f.write(
        "-- Generated by scripts/refinement/facts.sh. Do not edit.\n\n"
        "import Std.Tactic.BVDecide\n\n"
        "/-! The definitions shared by the theorems solar's Lean translator writes. -/\n\n"
        "namespace SolidCore.Refinement.Facts\n\n"
        "/-- An SMT-LIB array `store`: `m` with index `i` mapped to `v`. -/\n"
        + STORE
        + "\nend SolidCore.Refinement.Facts\n"
    )
root = ["-- Generated by scripts/refinement/facts.sh. Do not edit.", ""]
root += [f"import SolidCore.Refinement.Facts.{m}" for m in modules]
root += [
    "",
    "/-!",
    "# solar's analysis facts on the refinement corpus",
    "",
    "One module per `scripts/refinement/corpus` contract, each theorem one recorded MIR fact;",
    "see `scripts/refinement/FACTS.md` for what they mean.",
    "-/",
    "",
]
with open(f"{out}.lean", "w") as f:
    f.write("\n".join(root))
EOF

if (( check )); then
  if ! git diff --exit-code -- "$out" "$out.lean"; then
    echo "error: generated facts differ from the checked-in files; run scripts/refinement/facts.sh" >&2
    exit 1
  fi
  if [[ -n "$(git ls-files --others --exclude-standard -- "$out" "$out.lean")" ]]; then
    echo "error: untracked generated files in $out" >&2
    exit 1
  fi
fi
