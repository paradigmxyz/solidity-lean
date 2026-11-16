# InvOkFlat certify rerun r2: ABORTED-env

The rerun's single permitted restart was killed when the host machine restarted. It was still in the package prebuild. The last log line was `[6170/6180] Built EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Fors` at 2026-11-16 06:09 UTC. Neither `cargo build` nor `certify` ran. No receipts were written, and there is no verdict.

The build cache survived both kills: the restart resumed near step 5640 and got through about 530 more modules before it was killed.

InvOkFlat has no verdict and is parked. Another attempt needs a new decision and must run under a tracked keepalive. Details are in `r2-aborted-env.json`.
