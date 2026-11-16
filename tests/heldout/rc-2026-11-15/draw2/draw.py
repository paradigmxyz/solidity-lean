#!/usr/bin/env python3
"""Second held-out draw for the 2026-11-15 candidate: a mechanical, seeded draw.

Usage: python3 -I draw.py SOLAR_CHECKOUT SBE_CHECKOUT SOLC SEED_HEX > draw.json

Every .sol file under contracts/src of the Solidity by Example checkout, in sorted path order,
is a candidate unless a rule below excludes it. A candidate is eligible when its own file, unedited,
passes the generic driver's source envelope (tools/certify/generic.py envelope(), contract=None,
no invariants, natspec=False) with the pinned solc. Eligible files are ranked by
sha256(SEED_HEX + "\n" + path) as hex, ascending; the first two are H4 and H5.
"""
import hashlib, json, pathlib, re, sys

solar, sbe, solc, seed = sys.argv[1:5]
sys.path.insert(0, str(pathlib.Path(solar) / "tools/certify"))
import generic  # noqa: E402

# Fixed before the draw: the first set and the exclusions SELECTION.md already named.
USED = {"contracts/src/state-variables/SimpleStorage.sol",
        "contracts/src/view-and-pure-functions/ViewAndPureFunctions.sol",
        "contracts/src/mapping/Mapping.sol"}
EXCLUDED_NAME = re.compile(r"(?i)(counter|erc20|uniswap|flag)")

root = pathlib.Path(sbe)
rows = []
for f in sorted(root.glob("contracts/src/**/*.sol")):
    rel = str(f.relative_to(root))
    text = f.read_text()
    row = {"path": rel, "sha256": hashlib.sha256(text.encode()).hexdigest()}
    if rel in USED:
        row["verdict"] = "excluded: in the first set"
    elif EXCLUDED_NAME.search(rel):
        row["verdict"] = "excluded: name matches the fixed exclusion list"
    elif "SPDX-License-Identifier: MIT" not in text:
        row["verdict"] = "excluded: not SPDX MIT"
    else:
        try:
            ast, contracts = generic.solc_ast(solc, f.resolve())
            contract, fns, _ = generic.envelope(text, ast, contracts, None, None, False)
            row["verdict"] = "eligible"
            row["contract"] = contract
            row["functions"] = [fn["sig"] for fn in fns]
        except generic.Blocked as e:
            reasons = e.args[0] if e.args else []
            row["verdict"] = "outside: " + "; ".join(sorted({r.get("feature", "?") for r in reasons})) if isinstance(reasons, list) else "outside: " + str(reasons)[:200]
        except generic.Failed as e:
            row["verdict"] = "outside: " + str(e)[:200]
        except Exception as e:  # recorded, never hidden
            row["verdict"] = "error: " + type(e).__name__ + ": " + str(e)[:200]
    rows.append(row)

eligible = [r for r in rows if r["verdict"] == "eligible"]
for r in eligible:
    r["rank_key"] = hashlib.sha256((seed + "\n" + r["path"]).encode()).hexdigest()
ranked = sorted(eligible, key=lambda r: r["rank_key"])
json.dump({"seed": seed, "candidates": len(rows), "eligible": len(eligible),
           "ranked": [r["path"] for r in ranked], "H4": ranked[0]["path"] if ranked else None,
           "H5": ranked[1]["path"] if len(ranked) > 1 else None, "rows": rows}, sys.stdout, indent=1)
print()
