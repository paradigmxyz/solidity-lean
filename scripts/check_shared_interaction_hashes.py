#!/usr/bin/env python3
"""Guarantee the extracted shared-interaction package has not drifted.

The `evm-interaction` sibling package vendors evm-compiler's
`EvmCompiler/Simulation/*.lean` verbatim so both repos program against a
definitionally identical composition alphabet (Query/Answer/OpenWorld/ForwardRel).
This script proves byte-for-byte identity between the sibling's copies and
evm-compiler's live sources. It reads `../evm-compiler` read-only and never
writes to it.

Exit 0 iff every tracked Simulation file matches; non-zero with a diff summary
otherwise. Run from this repo root (or anywhere: paths are resolved relative to
this file).
"""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path

# Repo layout: this file lives at <solidity-lean>/scripts/.
REPO = Path(__file__).resolve().parent.parent
SIBLING = REPO.parent / "evm-interaction"
UPSTREAM = REPO.parent / "evm-compiler"

# The verbatim-extracted files, relative to each package root.
TRACKED = [
    "EvmCompiler/Simulation/Interaction.lean",
    "EvmCompiler/Simulation/OpenWorld.lean",
    "EvmCompiler/Simulation/Outcome.lean",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    if not UPSTREAM.is_dir():
        print(f"shared_interaction_hashes=skip (no upstream at {UPSTREAM})")
        # Not a hard failure: the check is only meaningful when the reference
        # checkout is present. CI with the reference present will enforce it.
        return 0
    if not SIBLING.is_dir():
        print(f"shared_interaction_hashes=fail (no sibling package at {SIBLING})")
        return 1

    mismatches = 0
    for rel in TRACKED:
        theirs = UPSTREAM / rel
        ours = SIBLING / rel
        if not theirs.exists():
            print(f"  {rel}: MISSING upstream ({theirs})")
            mismatches += 1
            continue
        if not ours.exists():
            print(f"  {rel}: MISSING sibling ({ours})")
            mismatches += 1
            continue
        th, oh = sha256(theirs), sha256(ours)
        if th == oh:
            print(f"  {rel}: ok ({th[:12]})")
        else:
            print(f"  {rel}: DRIFT sibling={oh[:12]} upstream={th[:12]}")
            mismatches += 1

    print("tracked_files=" + str(len(TRACKED)))
    print("mismatches=" + str(mismatches))
    print("shared_interaction_hashes=" + ("pass" if mismatches == 0 else "fail"))
    return 0 if mismatches == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
