# tools/pool: Lean build workers

Scripts that turn a fresh Linux machine (a short-lived bare-metal box, or any Hand) into a
solidity-lean build worker: the pinned Lean toolchain, Mathlib's prebuilt cache, a checkout of one
commit, and CI's builds run with as many Lean threads as the machine can take, each step reporting
wall time and peak memory. Build outputs pack into one archive that another lane restores to start
warm.

| File | What it does |
| --- | --- |
| `bootstrap.sh <sha\|branch> [--dir DIR] [--with-rust] [--no-cache]` | system packages, elan and the `lean-toolchain` toolchain, a checkout of the commit (full 40-character SHA or a branch), `lake exe cache get`. `--with-rust` adds Rust (the generated Uniswap V2 steps and the proof checks build solar). Re-running on the same DIR moves it to the new commit and keeps `.lake`. |
| `build.sh [--dir DIR] [--threads N] ci\|ci-gen\|audit` | CI's build commands, read from `.github/workflows/refinement.yml` at the checked-out commit by `ci_steps.py`, in CI's order and with CI's `-KleanMemory` caps but `LEAN_NUM_THREADS=N`. `ci`: the steps over committed sources. `ci-gen`: every build step, the Uniswap V2 generators included. `audit`: the axiom audit and `scripts/refinement/check.sh`. |
| `build.sh [--dir DIR] Mod.Name ...` | `lake build -KleanMemory=6000` of the given targets or modules (`--memory MB` changes the cap). |
| `build.sh [--dir DIR] --check path/File.lean` | `lake env lean -M 6000` on one file. |
| `pack.sh [--dir DIR] [--scope all\|project] [--out FILE]` | tar + zstd of `.lake` (`all`) or only `.lake/build` (`project`). |
| `unpack.sh FILE [--dir DIR] [--force]` | restores a pack onto a checkout; refuses one made at another `lake-manifest.json` or `lean-toolchain`. |

Defaults: `DIR` is `$POOL_ROOT/solidity-lean`, `POOL_ROOT` is `~/pool`, packs go to
`$POOL_ROOT/packs/<sha12>-<scope>.tar.zst`. `--threads` defaults to one per CPU, at most one per
5 GB of RAM. Every step prints `exit, wall seconds, largest process's peak RSS` (GNU time), and
the run ends with the machine-wide peak of used memory (sampled each second). Each run appends a
JSON line to `DIR/.lake/pool-report.jsonl`. The scripts run from anywhere: they need only
`--dir`.

## Measured at f8a4a744 (2026-11-14)

One m4-metal-small box (AMD EPYC 4244P, 12 threads, 61 GB, NVMe), cold: no `.lake`, no caches.

| Phase | Wall | Peak (machine / largest process) |
| --- | --- | --- |
| `bootstrap.sh --with-rust` (packages, elan, Rust, checkout, toolchain, Mathlib cache 63 s) | 82 s | |
| `build.sh ci` (4 steps, 3,100+ jobs) | 1,373 s (22.9 min) | 9.9 GiB / 5.4 GiB |
| `build.sh ci-gen` on top (the 4 Uniswap V2 steps: solc, two solar builds, generation, checks) | 1,318 s (22.0 min) | 21.3 GiB / 5.9 GiB |
| `build.sh audit` (axiom audit 57 s, `check.sh` 429 s) | 486 s (8.1 min) | 9.0 GiB / 4.2 GiB |
| Whole CI job, cold | about 54 min | |
| Re-run of `ci` in the same DIR (no-op) | 14 s | 1.5 GiB |

All steps exited 0. For comparison, GitHub CI's run of the same commit (16 GB runner,
`LEAN_NUM_THREADS=2`, starting from a restored `.lake` cache) took 81 min. The same `build.sh ci`
on the hosted Hand (5 CPUs, 14 GB, `--threads 1`, cold) had not finished its second step after 81
minutes (the box finished all four in 23). The box was mostly idle (load 1 to 3 of 12) during the
long serial modules (`Contracts.VerifyCounter.Source`'s step takes 983 s of the 1,373), so a
second lane on the same box costs little wall time.

Packs of that tree:

| Scope | Raw | Packed (zstd -3, 12 threads) | Pack | Restore | Lane warm (fresh checkout, restore, `build.sh ci`) |
| --- | --- | --- | --- | --- | --- |
| `all` | 10.56 GiB | 2.79 GiB | 8 s | 11 s | 53 s, at another path (bootstrap 2 s, restore 11 s, `build.sh ci` 33 s) |
| `project` | 2.86 GiB | 0.63 GiB | 2 s | 2 s | 262 s (bootstrap with cache get 69 s, then EthLib's and evmyul's outputs rebuild: 188 s) |

The `all` pack, made under `~/pool/solidity-lean`, restored warm under `~/lane2/sl`, so the
path does not matter. `.lake/packages` (Mathlib's
oleans, EthLib's native objects) is 8.5 of the 10.56 GiB.

Moving packs between machines: `copy_files` from a box Hand to the hosted Hand ran at about
3.1 MiB/s (the 0.63 GiB project pack in 210 s); the 2.79 GiB `all` pack would take about 15 min,
longer than one exec cell lasts, and two attempts were cut off. Split it first (`split -b 512M`)
and copy the parts in separate calls, or restore it only between lanes on the same box. A plain
HTTP pull over the tailnet from the hosted Hand to a box did not connect.

## Use from an agent thread

1. Create a box and attach it as a Hand (boxctl app; delete it when done, it costs money):

   ```js
   const box = await tools.boxctl__create_box({ name: "leanpool-" + hex4, plan: "f4-metal-small", region: "FRA2",
     keep_alive: "2h", labels: { requester: "<who asked>" }, wait: true });
   // On SERVERS_OUT_OF_STOCK: get_box, delete_box that name, then try m4-metal-small/FRA,
   // f4-metal-medium/FRA2, m4-metal-medium/FRA, m4-metal-large/FRA2 with a fresh name.
   const { hand_id } = await tools.attach_box({ box: box.result.box.name });
   ```

2. Fetch the scripts and bootstrap (on the box, `tools.Bash({ hand: hand_id, command })`):

   ```sh
   mkdir -p ~/pooltools && cd ~/pooltools
   for f in common.sh bootstrap.sh build.sh ci_steps.py pack.sh unpack.sh; do
     curl -fsSLO "https://raw.githubusercontent.com/paradigmxyz/solidity-lean/alpharush/lean-pool/tools/pool/$f"
   done
   chmod +x *.sh *.py
   ~/pooltools/bootstrap.sh <full-sha> --with-rust
   ```

   (Or `copy_files` the directory from a Hand that has the branch.)

3. Build. Long runs go in the background, and their logs are read later:

   ```sh
   nohup ~/pooltools/build.sh ci-gen > ~/build.log 2>&1 &   # or: ci, audit, a module, --check FILE
   grep '\[pool' ~/build.log                                 # step results and the summary
   ```

   Several lanes on one box: `bootstrap.sh <sha> --dir ~/lane2/sl --no-cache`, then
   `unpack.sh ~/pool/packs/<sha12>-all.tar.zst --dir ~/lane2/sl` and build with
   `--dir ~/lane2/sl --threads N` (split the CPUs between lanes; peaks stay under 6 GB a module).

4. Pack for reuse (`pack.sh --scope all`), then `tools.boxctl__delete_box({ name })`.

On the hosted Hand (14 GB): `build.sh --threads 1`, and keep 10 GB of disk free. `bootstrap.sh`
retries elan through the HTTPS proxy's IP address when elan cannot resolve the proxy's short
cluster name.

## Limits

- The workers build and check: they prove nothing new. A green `build.sh ci-gen` and `audit` is
  the same evidence CI gives at that commit, no more.
- Packs hold compiled outputs of the generated Uniswap V2 port (GPL-3.0). Keep them on Tempo's
  workers; never commit or publish them.
- `ci_steps.py` reads the workflow by indentation. If a step's layout changes, check
  `python3 tools/pool/ci_steps.py .github/workflows/refinement.yml ci-gen` against the workflow.
- `unpack.sh` restores over the directory without removing outputs the pack lacks.
