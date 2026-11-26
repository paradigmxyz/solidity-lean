# ERC20 ACCEPTANCE-1200 run: refused at step 1 (candidate binary)

The admitted run (ACCEPTANCE-1200.md at 41e6b29b) stops before any slot. No box was created.

Step 1 of the plan rebuilds solar f71b7554 and requires sha256 15808eeef2f5d5d021372d43a36ef491492cc8b2fc84b2c3b97a666a736381db,
which slot.sh and prep.sh also enforce. The rebuild, done as indep_build.sh does (same absolute paths
/home/hand/work/solar-f71 and /home/hand/work/solar-f71-target, CARGO_HOME /home/hand/.cargo, rustc
1.100.0 (0ef1bc386 2026-11-09), CARGO_BUILD_JOBS=4, RUSTFLAGS unset, `cargo build --release --locked --bin solar`,
source tree caad2955, Cargo.lock eb1a7cf2, clean), exits 0 and hashes to
166137ef66c1d792afd5b39bf5e3a1b02402f6c4484032f8b4115d926dd1245a: DIFFERS from 15808eee.

Cause: the binary embeds its build time (crates/config/build.rs, VERGEN_BUILD_TIMESTAMP; this build
reports "Build Timestamp: 2026-11-26T17:11:37.918634588Z"), so no rebuild can reproduce 15808eee,
and the only copy of that file was on a machine that no longer exists.

What the rebuild does reproduce: its `-Ogas --evm-version osaka --emit bin-runtime` of the ported
UniswapV2ERC20.sol (sha256 14da00cd…ac80b) is 1200 bytes, sha256
31f5c33cf15e660cf99ef9a9629a3b09fd48cb93fb983ad128d423f7ce11b420, byte-equal to `runtimeBytes` in
Certified/erc20_any/Statement.lean at 1f0db760.

Proceeding needs a new candidate pin (CANDIDATE_SHA256, an environment override in slot.sh, shard.sh,
prep.sh and run.sh); that is a change to the admitted pins and is not made here.
