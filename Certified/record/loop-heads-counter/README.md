# Loop-head manifest of Counter

This is the loop-head manifest that `solar-verify --emit-loop-heads` writes for `Counter.sol`. For every loop that verification reaches, it maps each SSA term at the loop's head, as the loop obligations name it, to what it denotes in the source. A state variable gets its storage slot, offset and type from the compiler's storage layout. Parameters, return variables and locals are labeled as such.

- solar: branch `alpharush/t1-loop-heads` @ fd53f637ef69065f897a1760726c254ccd7f9aa2 (tree cc342302021a0477d405846bdebf450154eae511, parent 800d78a98b9e64612c742d5038e7e2ec35dd52b4).
- solar-verify: a debug build at that commit, sha256 53de6ab1735cb5f8942e3281c235f024b39c04a431c5387d72e673b0a9545663. The manifest's `compiler` field is `0.8.38+commit.fd53f637.solar.0.3.0-dev`.
- z3: 4.15.4.
- Source: `Counter.sol`, sha256 f1c87a334b8db31fc8f80541febeaf8617318d20b685634f44e26c74146ad326. This is the same file as `Verify/LoopSource/RC/inputs/Counter.sol`.

## Commands

```
SOLAR_VERIFY_Z3=z3 solar-verify --no-infer --emit-loop-heads Counter.loop-heads.json Counter.sol
SOLAR_VERIFY_Z3=z3 solar-verify --no-infer --check-loop-heads Counter.loop-heads.json Counter.sol
```

The emit run verified all 4 functions and exited 0. The check printed `loop-head manifest matches`. A manifest with another source sha256 or another slot fails the check with exit 1 and names the first field that differs, as in `checks.txt`.

## Counter.bump

`Counter.bump` has one loop, at line 26, column 9. The terms at its head are:

| variable | kind | head term | entry term | loop writes it | slot |
|---|---|---|---|---|---|
| count | storage | `count@27` | `count@17` | yes | 0, offset 0, t_uint256 |
| i | local | `i@28` | `0` | yes | none |
| n | param | `n@21` | `n@21` | no | none |

## Manifest scope

- The terms are those of the real verification run, the ones `--dump-lean` writes. Inference's trial runs record nothing.
- The terms depend on the options the manifest records (`--strict`, `--no-infer`, `--only`). For Counter, the run with inference on gives the same loop heads.
- The manifest binds one source file. A file that imports other files is refused, because its storage layout would need them.

## Tests

`verify-tests.*` is the full `cargo test -p solar-verify` run with z3 required. It exited 0, with 22 and 58 tests passing. One of those is the new `loop_heads` test, which checks three things:
- Counter's manifest matches `crates/verify/tests/cases/loop_heads/Counter.loop-heads.json` exactly.
- That manifest passes `--check-loop-heads`.
- A manifest with a wrong source sha256, or with `count` at slot 1, fails the check with exit 1 and names the field.

The repository's nextest runner was not installed on this machine, so the suite ran under `cargo test`.
