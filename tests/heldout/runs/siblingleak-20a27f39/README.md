# SiblingLeak through the generic driver: REJECTED by its spec

The cold run of [negative/SiblingLeak.sol](../../negative/SiblingLeak.sol) through solar's generic
driver. Its postcondition `x <= 5 ==> level == 1` is false: the code stores 2 there.

Verdict (the last line of [driver.log](driver.log)), exit 1:

```
REJECTED: spec: set_meets0 does not check: omega could not prove the goal: (SpecConnect.lean:67)
```

## Pins

| what | value |
|---|---|
| driver | paradigmxyz/solar alpharush/t1-generic-driver at 20a27f39685284bea5a0fe40a7fed0437cfcf694 (clean) |
| solar binary | sha256 030139549f0be4279e49d45c9a000a9d79976ed97facfcac1e9719d617fb833d; `--version` reads commit 98693939, the compiler sources being unchanged since |
| solidity-lean | base 44572c150176365fa5e0d56ae6c59a7a443f8122; the driver's local input commit c20894629523c5a1c749daa3d5f6a7bf541435d7 adds only [record/inputs](record/inputs) |
| Lean | leanprover/lean4:v4.35.0, toolchain digest 953aa1e72283c07686567bb71eeb3fca202baafe2958a7e57987d3b8c4434c25 |
| solc | 0.8.35, sha256 fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4 |
| source and spec | natspec, sha256 7e2f4c33f69309afa5ba3464dd1eb172b5b81fe33cf98d9bc61d3a45e4b1eef2 |
| options | `-Ogas --evm-version osaka`; LEAN_MEMORY=6000, CERTIFY_CLEAN_BUILD=1, LEAN_NUM_THREADS=1 |
| run | 2026-11-15 08:15:17Z to 08:26:35Z; receipt: exit 1, peak RSS 5271 MB, 679 s |

## Files

* [record/](record): the driver's record directory, as written: `record.json`, `certify.log`, the
  source and the generated inputs. Every file listed in `record.json` `.run_files` matches its
  digest.
* [driver.log](driver.log): the driver's whole output.
* [evidence/SpecConnect.lean](evidence/SpecConnect.lean) and [evidence/Spec.lean](evidence/Spec.lean):
  the generated SpecConnect module that fails at line 67 (`set_meets0`), and solar-verify's export
  of the spec. They are evidence of the rejection, not checked artifacts: no statement module was
  built, so nothing here is a theorem.
* [SHA256SUMS](SHA256SUMS): every file of this directory.

The positive twin, [negative/SiblingOk.sol](../../negative/SiblingOk.sol) (same code, true
postcondition), runs in the driver owner's cold queue on the same pins. Until it certifies there,
this run shows that the false spec is refused, not that the refusal is specific to it.
