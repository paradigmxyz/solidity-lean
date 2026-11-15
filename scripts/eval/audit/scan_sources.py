#!/usr/bin/env python3
"""Scan Lean sources for constructs that trust code the kernel does not check, or skip proofs.

Comments and string literals are stripped first. A hit on a line listed in allow.txt
(`path<TAB>pattern<TAB>reason`) is reported but does not fail the scan."""
import os, re, sys

PATTERNS = [
    ("native_decide", r"\bnative_decide\b"),
    ("bv_decide", r"\bbv_decide\b"),
    ("sorry", r"\bsorry\b"),
    ("admit", r"\badmit\b"),
    ("axiom", r"(^|\s)axiom\s"),
    ("ofReduceBool", r"\bofReduce(Bool|Nat)\b"),
    ("trustCompiler", r"\btrustCompiler\b"),
    ("implemented_by", r"\bimplemented_by\b"),
    ("extern", r"@\[\s*extern\b"),
    ("skipKernelTC", r"\bskipKernelTC\b"),
    ("cbv_at_star", r"\bcbv\b[^\n]*\bat\s*\*"),
    ("unsafe", r"\bunsafe\b"),
]

def strip(text):
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i); j = n if j < 0 else j
            i = j; continue
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth > 0:
            if text.startswith("-/", i):
                depth -= 1; i += 2; continue
            out.append("\n" if text[i] == "\n" else " "); i += 1; continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append('""' + "\n" * text.count("\n", i, j)); i = j + 1; continue
        out.append(text[i]); i += 1
    return "".join(out)

def load_allow(here):
    allow = []
    p = os.path.join(here, "allow.txt")
    if os.path.exists(p):
        for l in open(p, encoding="utf-8"):
            l = l.rstrip("\n")
            if l and not l.startswith("#"):
                parts = l.split("\t")
                allow.append((parts[0], parts[1]))
    return allow

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    allow = load_allow(here)
    bad = 0
    for path in sys.argv[1:]:
        text = strip(open(path, encoding="utf-8").read())
        rel = os.path.relpath(os.path.abspath(path), os.path.abspath(os.path.join(here, "../../..")))
        for ln, line in enumerate(text.split("\n"), 1):
            for name, pat in PATTERNS:
                if re.search(pat, line):
                    ok = any(rel == a and name == b for a, b in allow)
                    print(f"SCAN\t{rel}:{ln}\t{name}\t{'allowed' if ok else 'VIOLATION'}\t{line.strip()[:120]}")
                    bad += 0 if ok else 1
    print(f"scan: {bad} violation(s)")
    sys.exit(1 if bad else 0)

main()
