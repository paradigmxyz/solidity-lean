#!/usr/bin/env bash
# Cold replay of the evaluation modules (lane H).
#
#   scripts/eval/audit/cold_replay.sh [--save] [module-or-file ...]
#
# Builds a cold copy under /tmp: the repository's sources and the built .olean files of everything
# else are linked in, but no .olean of any Verify.Eval module is (the copy's Verify/Eval build
# directory starts empty). It then re-checks the selected Verify/Eval modules (default: all) from
# source in dependency order with scripts/eval/check.sh, writing each .olean into the cold copy
# only, so every module is checked against freshly re-checked eval dependencies, never stale ones.
# Each module is then audited from its cold .olean (#audit_axioms_module): every theorem's
# statement hash and transitive axioms. The result is compared with the manifest
# scripts/eval/audit/manifest.tsv (module, declaration, kind, statement hash, axioms):
# a changed hash or axiom set, a missing declaration, a failed check or a non-standard axiom fails
# the replay; new declarations are reported. --save writes the manifest instead of comparing
# (for the selected modules; rows of other modules are kept).
#
# Nothing outside /tmp is deleted or written, except the receipts and logs check.sh keeps in $HOME
# and, with --save, the manifest.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../../.." && pwd)"
manifest="$here/manifest.tsv"
save=0
[ "${1:-}" = --save ] && { save=1; shift; }
[ -f "$HOME/env.sh" ] && source "$HOME/env.sh"

cold="$(mktemp -d /tmp/eval-cold.XXXXXX)"
echo "cold copy: $cold"
# sources: link every top-level entry, then rebuild Verify and scripts as real directories
for e in "$repo"/* "$repo"/.[!.]*; do
  b="$(basename "$e")"
  case "$b" in .lake|.git|Verify|scripts) ;; *) ln -s "$e" "$cold/$b" ;; esac
done
cp -rs "$repo/Verify" "$cold/Verify"
# the eval sources themselves are real copies: lean resolves its input path, and a symlink into the
# repository would leave the cold root
rm -rf "$cold/Verify/Eval"; cp -r "$repo/Verify/Eval" "$cold/Verify/Eval"
mkdir -p "$cold/scripts/eval"
cp "$repo/scripts/eval/check.sh" "$cold/scripts/eval/check.sh"
cp -r "$repo/scripts/eval/audit" "$cold/scripts/eval/audit"
# build outputs: the packages as they are, the root's .olean files linked, Verify/Eval left out
mkdir -p "$cold/.lake/build/lib"
ln -s "$repo/.lake/packages" "$cold/.lake/packages"
cp -rs "$repo/.lake/build/lib/lean" "$cold/.lake/build/lib/lean"
rm -rf "$cold/.lake/build/lib/lean/Verify/Eval"   # symlinks inside /tmp only
[ -d "$repo/.lake/config" ] && cp -r "$repo/.lake/config" "$cold/.lake/config"
cd "$cold"

# the modules to replay, in dependency order (imports among Verify.Eval modules)
if [ $# -gt 0 ]; then
  sel=()
  for t in "$@"; do t="${t%.lean}"; sel+=("${t//\//.}"); done
else
  mapfile -t sel < <(find Verify/Eval -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort)
fi
mapfile -t order < <(python3 - "${sel[@]}" <<'PY'
import re, sys
sel = sys.argv[1:]
deps = {}
def imports(m):
    out = []
    for l in open(m.replace('.', '/') + '.lean', encoding='utf-8'):
        mm = re.match(r'\s*(?:public\s+)?import\s+(\S+)', l)
        if mm and mm.group(1).startswith('Verify.Eval.'):
            out.append(mm.group(1))
    return out
stack = list(sel)
while stack:
    m = stack.pop()
    if m in deps: continue
    deps[m] = imports(m)
    stack.extend(d for d in deps[m] if d not in deps)
done, order = set(), []
def visit(m, path=()):
    if m in done: return
    if m in path: raise SystemExit('import cycle at ' + m)
    for d in deps[m]: visit(d, path + (m,))
    done.add(m); order.append(m)
for m in sorted(deps): visit(m)
print('\n'.join(order))
PY
)
# the audit command itself is replayed first, from source like the rest
order=("Verify.Eval.H.Audit" $(printf '%s\n' "${order[@]}" | grep -v '^Verify.Eval.H.Audit$'))
echo "replaying ${#order[@]} module(s)"
mkdir -p "$cold/out"
status=0
: > "$cold/out/rows.tsv"
for m in "${order[@]}"; do
  f="${m//.//}.lean"
  o=".lake/build/lib/lean/${m//.//}.olean"
  mkdir -p "$(dirname "$o")"
  if ! EVAL_RECEIPTS="${EVAL_RECEIPTS:-$HOME/eval-receipts.jsonl}" scripts/eval/check.sh H-cold "$f" -o "$o" -Dprofiler=false > "$cold/out/$m.check.log" 2>&1; then
    echo "FAIL check $m (log $cold/out/$m.check.log)"; status=1; continue
  fi
  a="$cold/out/Audit_${m//./_}.lean"
  printf 'import Verify.Eval.H.Audit\nimport %s\n#audit_axioms_module %s\n' "$m" "$m" > "$a"
  if ! EVAL_RECEIPTS="${EVAL_RECEIPTS:-$HOME/eval-receipts.jsonl}" scripts/eval/check.sh H-cold "$a" -Dprofiler=false > "$cold/out/$m.audit.log" 2>&1; then
    echo "FAIL audit $m (log $cold/out/$m.audit.log)"; status=1; continue
  fi
  grep -P '^AXIOMS\t' "$cold/out/$m.audit.log" | sed "s|^AXIOMS|$m|" >> "$cold/out/rows.tsv"
  echo "ok   $m ($(grep -cP '^AXIOMS\t' "$cold/out/$m.audit.log") theorems)"
done

if [ $save = 1 ] && [ $status != 0 ]; then echo "not saving the manifest: a check or audit failed"; echo "cold replay: FAILED (copy kept in $cold)"; exit 1; fi
python3 - "$manifest" "$cold/out/rows.tsv" "$save" "${order[@]}" <<'PY'
import sys, os
manifest, rows, save, mods = sys.argv[1], sys.argv[2], sys.argv[3] == '1', set(sys.argv[4:])
def load(p):
    d = {}
    if os.path.exists(p):
        for l in open(p, encoding='utf-8'):
            if l.startswith('#') or not l.strip(): continue
            m, n, k, h, ax = (l.rstrip('\n').split('\t') + [''] * 5)[:5]
            d[(m, n)] = (k, h, ax)
    return d
old, new = load(manifest), load(rows)
if save:
    keep = {k: v for k, v in old.items() if k[0] not in mods}
    keep.update(new)
    with open(manifest, 'w', encoding='utf-8') as f:
        f.write('# module\tdeclaration\tkind\tstatement-hash\taxioms (scripts/eval/audit/cold_replay.sh --save)\n')
        for (m, n), (k, h, ax) in sorted(keep.items()):
            f.write(f'{m}\t{n}\t{k}\t{h}\t{ax}\n')
    print(f'manifest saved: {len(new)} rows for {len(mods)} module(s), {len(keep)} rows in all')
    sys.exit(0)
bad = 0
for key, (k, h, ax) in sorted(old.items()):
    if key[0] not in mods: continue
    if key not in new:
        print('MISSING', *key); bad += 1
    elif new[key][1] != h:
        print('STATEMENT CHANGED', *key, h, '->', new[key][1]); bad += 1
    elif new[key][2] != ax:
        print('AXIOMS CHANGED', *key, ax, '->', new[key][2]); bad += 1
for key in sorted(new):
    if key not in old: print('new (not in manifest)', *key)
print(f'manifest comparison: {bad} difference(s) over {sum(1 for k in old if k[0] in mods)} manifest rows')
sys.exit(1 if bad else 0)
PY
[ $? -ne 0 ] && status=1
echo "cold replay: $([ $status = 0 ] && echo PASSED || echo FAILED) (copy kept in $cold)"
exit $status
