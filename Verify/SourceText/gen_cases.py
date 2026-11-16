#!/usr/bin/env python3
"""Freeze G0's test cases: the sources, and the upstream frontend's reading of each.

For each case this writes Verify/SourceText/Cases/<Name>.sol (the exact bytes), and
Verify/SourceText/Cases/<Name>.lean with the bytes as a list and, when the pinned upstream
frontend accepts the source, its reading: solc's AST through scripts/solc_ast_to_lean_source.py,
solar-verify --emit-lean-spec's bundle, and solc --hashes' ABI. That reading is what G0's must
equal or differ from (Tests.lean). The mutations are fixed text edits of the two originals,
below; the script fails if an edit does not apply exactly once.

usage: gen_cases.py SOLC SOLAR_VERIFY FLAG_SOL
"""
import hashlib, json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(ROOT, "Verify", "SourceText", "Cases")
NS = "SolidCore.Verify.SourceText.Cases"
BT = chr(96)

def edit(src, old, new):
    assert src.count(old) == 1, (old, src.count(old))
    return src.replace(old, new)

def rename(src, names):
    for a, b in names:
        src = re.sub(r"\b%s\b" % re.escape(a), b, src)
    return src

def cases(flag, ledger):
    lr = ledger
    yield "LedgerRelay", lr
    yield "LedgerRelayBody", edit(lr, "stamp = 17;", "stamp = 18;")
    yield "LedgerRelaySpec", edit(lr, "stamp == 17", "stamp == 18")
    yield "LedgerRelayName", edit(lr, "function setPair(", "function setPairs(")
    yield "LedgerRelayCaller", edit(lr, "/// @custom:succeeds-if msg.value == 0\n    /// @custom:ensures left == a",
                                    "/// @custom:succeeds-if msg.sender == 0\n    /// @custom:ensures left == a")
    yield "LedgerRelayStorage", edit(lr, "uint256 public left;", "uint256 public left = 1;")
    yield "LedgerRelayRequire", edit(lr, "external {\n        left = a;", "external {\n        require(a == a);\n        left = a;")
    yield "LedgerRelaySwap", edit(lr, "        left = right;\n        right = marker;\n",
                                  "        right = marker;\n        left = right;\n")
    yield "LedgerRelayAlpha", rename(lr, [("LedgerRelay", "PairBridge"), ("left", "first"), ("right", "second"),
                                          ("stamp", "mark"), ("setPair", "store"), ("relay", "shift"),
                                          ("a", "p"), ("b", "q"), ("marker", "m")])
    layout = edit(lr, "contract LedgerRelay {\n", "// a comment\ncontract   LedgerRelay\n{\n\n")
    layout = edit(layout, "        left = a;\n", "      left=a;   // a\n")
    layout = edit(layout, "right == marker", "right==marker")
    layout = edit(layout, "    function relay(uint256 marker) external {", "    function relay( uint256 marker )\n        external\n    {")
    yield "LedgerRelayLayout", layout
    yield "Flag", flag
    yield "FlagBody", edit(flag, "raised = 1;", "raised = 2;")
    yield "FlagSpec", edit(flag, "raised == 1", "raised == 2")
    yield "FlagName", edit(flag, "function raise(", "function raises(")
    yield "FlagCaller", edit(flag, "/// @custom:succeeds-if msg.value == 0\n    /// @custom:ensures value == v",
                             "/// @custom:succeeds-if msg.sender == 0\n    /// @custom:ensures value == v")
    yield "FlagStorage", edit(flag, "uint256 public value;", "uint256 public value = 1;")
    yield "FlagRequire", edit(flag, "external {\n        value = v;", "external {\n        require(v == v);\n        value = v;")

def contract_of(src):
    return re.search(r"\bcontract\s+(\w+)", src).group(1)

def lean_bytes(b):
    rows = [", ".join(str(x) for x in b[i:i + 24]) for i in range(0, len(b), 24)]
    return "[\n  " + ",\n  ".join(rows) + "]"

def main():
    solc, verify, flag_path = sys.argv[1:4]
    flag = open(flag_path, "rb").read().decode()
    ledger = open(os.path.join(OUT, "LedgerRelay.sol"), "rb").read().decode()
    index = []
    for name, src in cases(flag, ledger):
        data = src.encode()
        sol = os.path.join(OUT, name + ".sol")
        if name != "LedgerRelay":
            open(sol, "wb").write(data)
        assert open(sol, "rb").read() == data
        rel = os.path.relpath(sol, ROOT)
        sha = hashlib.sha256(data).hexdigest()
        c = contract_of(src)
        ns = "%s.%s" % (NS, name)
        d = os.path.join(OUT, name)
        os.makedirs(d, exist_ok=True)
        for f in os.listdir(d):
            os.remove(os.path.join(d, f))
        imp = subprocess.run([sys.executable, os.path.join(ROOT, "scripts/solc_ast_to_lean_source.py"), rel,
                              "--contract", c, "--solc", solc, "--namespace", "SourceTextCases.%s.Imported" % name, "--body-only"],
                             cwd=ROOT, capture_output=True, text=True)
        spec_file = os.path.join(d, "Spec.lean")
        sv = subprocess.run([verify, "--emit-lean-spec", spec_file, "--lean-spec-module", ns + ".Spec", rel],
                            cwd=ROOT, capture_output=True, text=True)
        hashes = subprocess.run([solc, "--hashes", rel], cwd=ROOT, capture_output=True, text=True)
        upstream = imp.returncode == 0 and sv.returncode == 0 and hashes.returncode == 0
        entry = {"case": name, "file": rel, "bytes": len(data), "sha256": sha, "contract": c,
                 "importer": imp.returncode, "spec_export": sv.returncode, "solc_hashes": hashes.returncode}
        index.append(entry)
        imports = ["Verify.SourceText.Grammar"]
        body = ["/-- The exact bytes of %s%s%s (%d bytes, sha256 %s). -/" % (BT, rel, BT, len(data), sha),
                "def bytes : List Nat := " + lean_bytes(data), ""]
        if upstream:
            # importedSourceName holds the checkout's absolute path. It is not part of the reading
            # (Generic.Source has no name), so the frozen file records it repository-relative.
            text = re.sub(r'^def importedSourceName : String := ".*"$',
                          'def importedSourceName : String := "%s"' % rel, imp.stdout, flags=re.M)
            # The header solar's tools/certify/generic.py puts on the importer's --body-only output.
            open(os.path.join(d, "Imported.lean"), "w").write(
                "-- Generated by Verify/SourceText/gen_cases.py with scripts/solc_ast_to_lean_source.py. Do not edit.\n"
                "\nimport SolidCore.Solidity.Checked\n\nopen SolidCore.Solidity\n\n" + text)
            abi = []
            for line in hashes.stdout.splitlines():
                m = re.match(r"^([0-9a-f]{8}): (\w+)\(([^)]*)\)$", line)
                if m:
                    params = [p for p in m.group(3).split(",") if p]
                    assert all(p == "uint256" for p in params), line
                    abi.append(("%s(%s)" % (m.group(2), m.group(3)), int(m.group(1), 16), len(params)))
            abi.sort(key=lambda e: e[0].encode())
            imports += ["Verify.SourceText.Cases.%s.Imported" % name, "Verify.SourceText.Cases.%s.Spec" % name]
            abi_lean = ",\n    ".join('("%s", ⟨0x%08x, %s⟩)' % (s, sel, "[" + ", ".join(["(.uint 256)"] * n) + "]")
                                       for s, sel, n in abi)
            body += ["/-- The upstream frontend's reading: solc's AST through the importer, solar-verify's",
                     "spec export and solc's ABI (solc --hashes, sorted by signature); no constructor storage. -/",
                     "def upstream : Reading :=",
                     "  { unit := SourceTextCases.%s.Imported.importedSourceUnit, contract := \"%s\"," % (name, c),
                     "    abi := [\n    %s]," % abi_lean,
                     "    bundle := Spec.%s, storage := [] }" % c, ""]
            entry["abi"] = [[s, "0x%08x" % sel] for s, sel, n in abi]
        else:
            for f in os.listdir(d):
                os.remove(os.path.join(d, f))
            os.rmdir(d)
            body += ["/-- The upstream frontend does not accept this source (importer exit %d, spec export exit %d). -/"
                     % (imp.returncode, sv.returncode), "def upstreamAccepts : Bool := false", ""]
        open(os.path.join(OUT, name + ".lean"), "w").write(
            "-- Generated by Verify/SourceText/gen_cases.py. Do not edit.\n" +
            "".join("import %s\n" % i for i in imports) +
            "\nnamespace %s\n\nopen SolidCore.Verify.SourceText SolidCore.Solidity\n\n" % ns +
            "\n".join(body) + "\nend %s\n" % ns)
    with open(os.path.join(OUT, "index.json"), "w") as f:
        json.dump(index, f, indent=1)
        f.write("\n")
    write_selectors(index)
    for e in index:
        print(e["case"], e["sha256"][:12], "importer", e["importer"], "spec", e["spec_export"], "hashes", e["solc_hashes"])

def write_selectors(index):
    sigs = {}
    for e in index:
        for s, sel in e.get("abi", []):
            assert sigs.get(s, sel) == sel, s
            sigs[s] = sel
    sigs = sorted(sigs.items(), key=lambda kv: kv[0].encode())
    out = ["-- Generated by Verify/SourceText/gen_cases.py. Do not edit.",
           "import SolidCore.Refinement.KernelRfl", "import SolidCore.Solidity.Checked", "",
           "/-!", "# The selectors of the cases' signatures, each by Keccak-256 once, then by table", "",
           "Each value is solc's (" + BT + "solc --hashes" + BT + "); the kernel checks it against SolidCore's own",
           BT + "ABI.selectorFromSignature" + BT + ", and " + BT + "selector_eq" + BT + " lets the tests' checks call the table.",
           "-/", "", "namespace SolidCore.Verify.SourceText.Cases.Selectors", ""]
    for i, (s, sel) in enumerate(sigs):
        out += ["def sig%d : SolidCore.Solidity.Shared.Word :=" % i,
                '  SolidCore.Solidity.Source.ABI.selectorFromSignature "%s"' % s, "",
                "def sel%d : SolidCore.Solidity.Shared.Word := %s" % (i, sel), "",
                "kernel_rfl sig%d_eq sig%d sel%d" % (i, i, i), ""]
    out += ["/-- " + BT + "ABI.selectorFromSignature" + BT + ", with the cases' signatures by table. -/",
            "def table (s : String) : SolidCore.Solidity.Shared.Word :="]
    for i, (s, sel) in enumerate(sigs):
        out.append('  %sif s = "%s" then sel%d' % ("" if i == 0 else "else ", s, i))
    out += ["  else SolidCore.Solidity.Source.ABI.selectorFromSignature s", "",
            "theorem selector_eq : SolidCore.Solidity.Source.ABI.selectorFromSignature = table := by",
            "  funext s", "  unfold table"]
    # One case per signature: on it, the table's value is the kernel-checked selector; off it,
    # the next condition. Explicit if_pos/if_neg rewrites, so no simp search over String equality.
    for i, (s, sel) in enumerate(sigs):
        out += ["  by_cases h%d : s = \"%s\"" % (i, s),
                "  · rw [if_pos h%d]; subst h%d; exact sig%d_eq" % (i, i, i),
                "  rw [if_neg h%d]" % i]
    out += ["", "end SolidCore.Verify.SourceText.Cases.Selectors", ""]
    open(os.path.join(OUT, "Selectors.lean"), "w").write("\n".join(out))

main()
