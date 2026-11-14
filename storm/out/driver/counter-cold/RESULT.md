# driver: cold Counter run with the published driver (whole closure replayed)

The driver of solar bcd1ae63 (the same tools/certify and scripts/certify as #2637 head 697fc686
with restore-697's three helpers) certified Counter from a clean build in one run:

    CERTIFY_CLEAN_BUILD=1 CERTIFY_REPLAY_BATCH=4 LEAN_NUM_THREADS=2 LEAN_MEMORY=8000 \
      scripts/certify Certified/counter/counter.sol --require-headline --require-final

- exit 0, 10703 s wall (2.97 h), peak one-process RSS 7840 MiB, peak system used 8636 of 14531 MiB
  (counter-cold.receipt.json); target/debug and the git packages' builds were removed first.
- Final line: `CERTIFIED counter (Counter): equivalence, termination, spec and resources by
  Certified.counter.Final.final`, with no caveats.
- check_final: `Certified.counter.Final.final : Certified.counter.Final.Statement`, axioms
  [propext, Classical.choice, Quot.sound].
- Replay (replay.receipt.json): closure 3905 modules, 3905 replayed by leanchecker in this run,
  0 trusted by directory, 0 unaccounted.
- Step 7: negative.sh and final_neg.sh variants all refused (counter-cold.log).

Earlier attempts and why they stopped: an unbuilt git package made a sandboxed step fail with a
read-only file system (fixed by prebuild_packages); the kernel ran out of memory at
LEAN_MEMORY=5000; solc was not installed; the fourth was killed from outside during the replay.
