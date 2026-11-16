# acc5-flag on driver 800d78a9, aborted

acc5-flag certified Flag.sol (sha256 4ce5cf9a87520dc956a1e7366d5f646a07739832e44a3d8dec2eb656deb6388d) on driver 800d78a98b9e64612c742d5038e7e2ec35dd52b4, base 44572c15. None of its three attempts reached a verdict. This record is ABORTED, with no verdict, and is not a result.

- Attempt 1 started at 2026-11-16T00:41:50Z. The machine paused around 00:53Z, which killed it. Its files are in acc4-siblingok-aborted/.
- Attempt 2 started at 2026-11-16T01:02:09Z. The machine paused at 03:20:08Z, which killed it during the kernel closure replay (3966 modules). Files: attempt2.*. Peak tree RSS: 8793 MiB.
- Attempt 3 started at 2026-11-16T03:20:39Z. It passed the probe, the Final build and check_final (axioms propext, Classical.choice, Quot.sound), and was in the closure replay of 3966 modules (0 trusted by directory). It was stopped on purpose at 04:48:54Z because the driver pin moved to 0479b90a422245bf77facc51ea17b960ed5c5851. Files: attempt3.*. Peak tree RSS: 8754 MiB.

Flag is rerun as rc2-acc5-flag on driver 0479b90a (base 49d1d7f5).
