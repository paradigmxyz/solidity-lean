#!/usr/bin/env bash
# Kernel check of the finite ERC20 premise for the real keccak256, for a list of addresses.
#
#   finite_check.sh [--single] <balSlot> <allowSlot> <addr>...
#
# Proves KeccakSep (erc20Preimages <balSlot> <allowSlot> [<addr>, ...].toFinset)
# (Verify/Spec/HashScopeFiniteCheck.lean): the n balance, n outer and n^2 inner allowance preimages.
# By default each of the 2n + n^2 images is its own declaration ('keccakWord p = v' by
# 'decide +kernel'), the values computed here by a Python Keccak-256 and each re-checked by the
# kernel, and the premise follows by 'erc20Sep_of_images' with one 'imagesCheck' evaluation.
# --single instead proves it by one evaluation of the checker, 'erc20SepCheck_sound
# (by decide +kernel)': the kernel keeps about 0.4 GB per sponge, so that is for one or two
# addresses only. Slots are below 2^128, addresses below 2^160 (decimal or 0x hex), and distinct
# (repeated addresses repeat images, which 'imagesCheck' refuses). Checks the axioms; exits 0 when
# the kernel accepts, 1 when the check or the axiom audit fails, 2 on malformed input. Run from the
# repository root after 'lake build Verify.Spec.HashScopeFiniteCheck'. LEAN_MEMORY (MB, default
# 6000) caps the Lean process as CI does.
set -euo pipefail

die() { echo "REFUSED $*" >&2; exit 2; }

single=0
if [ "${1:-}" = "--single" ]; then single=1; shift; fi
[ $# -ge 3 ] || die "takes [--single] <balSlot> <allowSlot> <addr>..."

dir=$(mktemp -d); trap 'rm -rf "$dir"' EXIT
cat > "$dir/keccak.py" <<'EOF'
#!/usr/bin/env python3
"""Keccak-256 (the Ethereum variant, padding 0x01) of byte strings."""

RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
      0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
      0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
      0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
      0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
      0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
ROT = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56],
       [27, 20, 39, 8, 14]]
M = (1 << 64) - 1


def rol(x, r):
    r %= 64
    return ((x << r) | (x >> (64 - r))) & M if r else x


def f1600(a):
    for rc in RC:
        c = [a[x][0] ^ a[x][1] ^ a[x][2] ^ a[x][3] ^ a[x][4] for x in range(5)]
        d = [c[(x - 1) % 5] ^ rol(c[(x + 1) % 5], 1) for x in range(5)]
        a = [[a[x][y] ^ d[x] for y in range(5)] for x in range(5)]
        b = [[0] * 5 for _ in range(5)]
        for x in range(5):
            for y in range(5):
                b[y][(2 * x + 3 * y) % 5] = rol(a[x][y], ROT[x][y])
        a = [[b[x][y] ^ ((~b[(x + 1) % 5][y]) & b[(x + 2) % 5][y]) for y in range(5)]
             for x in range(5)]
        a[0][0] ^= rc
    return a


def keccak256(msg: bytes) -> bytes:
    rate = 136
    p = bytearray(msg) + b"\x01" + b"\x00" * ((-len(msg) - 2) % rate) + b"\x80"
    if len(p) % rate:  # one byte of padding: 0x81
        p = bytearray(msg) + b"\x81"
    a = [[0] * 5 for _ in range(5)]
    for i in range(0, len(p), rate):
        blk = p[i:i + rate]
        for j in range(rate // 8):
            x, y = j % 5, j // 5
            a[x][y] ^= int.from_bytes(blk[8 * j:8 * j + 8], "little")
        a = f1600(a)
    out = b"".join(a[j % 5][j // 5].to_bytes(8, "little") for j in range(4))
    return out


def word(b: bytes) -> int:
    return int.from_bytes(b, "big")


def slot(k: int, s: int) -> int:
    """keccak256(k . s) as a word: the slot of m[k] for a mapping m at slot s."""
    return word(keccak256(k.to_bytes(32, "big") + s.to_bytes(32, "big")))


if __name__ == "__main__":
    assert keccak256(b"").hex() == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    print(hex(slot(0, 0)))
EOF
cat > "$dir/gen.py" <<'EOF'
import sys
sys.path.insert(0, sys.argv[1])
import keccak as K

def num(s, bits):
    try:
        v = int(s, 16) if s.lower().startswith("0x") else int(s, 10)
    except ValueError:
        sys.stderr.write(f"REFUSED not a number: {s}\n"); sys.exit(2)
    if not (0 <= v < 2 ** bits):
        sys.stderr.write(f"REFUSED out of range (2^{bits}): {s}\n"); sys.exit(2)
    return v

single = sys.argv[2] == "1"
b, a = num(sys.argv[3], 128), num(sys.argv[4], 128)
As = [num(x, 160) for x in sys.argv[5:]]
if len(set(As)) != len(As):
    sys.stderr.write("REFUSED repeated address\n"); sys.exit(2)
if b == a:
    sys.stderr.write("REFUSED balance and allowance slots are equal\n"); sys.exit(2)
h = hex
addrs = ", ".join(h(x) for x in As)
out = ["import Verify.Spec.HashScopeFiniteCheck", "open SolidCore.Spec SolidCore.Spec.TrustedBase", ""]
stmt = f"KeccakSep (erc20Preimages {b} {a} [{addrs}].toFinset)"
print(f"PREMISE {stmt}", file=sys.stderr)
if single:
    out.append("set_option maxRecDepth 100000 in")
    out.append(f"theorem finite_premise : {stmt} :=\n  erc20SepCheck_sound (by decide +kernel)")
else:
    lem, H = [], []
    def thm(name, k, s, v):
        out.append("set_option maxRecDepth 100000 in")
        out.append(f"theorem {name} : keccakWord (mappingPreimage {h(k)} {h(s)}) =\n    {h(v)} := by\n  decide +kernel\n")
        lem.append(name)
    outs = [K.slot(o, a) for o in As]
    for i, k in enumerate(As):
        v = K.slot(k, b); thm(f"bal{i}", k, b, v); H.append(v)
    for i, o in enumerate(As):
        thm(f"out{i}", o, a, outs[i]); H.append(outs[i])
    for i in range(len(As)):
        for j, s in enumerate(As):
            v = K.slot(s, outs[i]); thm(f"inn{i}_{j}", s, outs[i], v); H.append(v)
    out.append("set_option maxRecDepth 100000 in")
    out.append(f"theorem finite_images : (erc20ListBy keccakWord {b} {a} [{addrs}]).map keccakWord =\n"
               f"    [{', '.join(h(v) for v in H)}] := by\n"
               f"  simp only [erc20ListBy, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,\n"
               f"    List.cons_append, List.nil_append, List.append_nil, {', '.join(lem)}]\n")
    out.append("set_option maxRecDepth 100000 in")
    out.append(f"theorem finite_premise : {stmt} :=\n  erc20Sep_of_images finite_images (by decide +kernel)")
out.append("#print axioms finite_premise")
print("\n".join(out))
EOF
python3 -I "$dir/gen.py" "$dir" "$single" "$@" > "$dir/Check.lean" || exit 2

if ! out=$(lake env lean -M "${LEAN_MEMORY:-6000}" "$dir/Check.lean" 2>&1); then
  echo "$out" >&2; echo "CHECK failed"; exit 1
fi
echo "$out"
ax=$(echo "$out" | sed -n "s/.*depends on axioms: \[\(.*\)\]/\1/p")
[ -n "$ax" ] || { echo "CHECK no axiom report"; exit 1; }
for x in $(echo "$ax" | tr ',' ' '); do
  case "$x" in propext|Classical.choice|Quot.sound) ;; *) echo "CHECK axiom refused: $x"; exit 1 ;; esac
done
echo "CHECK kernel accepted"
