# solc 0.8.35 vs solidity-lean — Integer Arithmetic / Shifts / Conversions review

Scope: checked exponentiation, shift/bitwise semantics, signed div/mod edges,
mulmod/addmod, integer type conversions (truncation/sign-extension), unchecked,
unary negation. Ground truth: pinned solc 0.8.35 (legacy codegen, optimizer off)
via Forge; compared against the solidity-lean interpreter (`#eval` of the actual
`SolidCore.Solidity.Source` primitives).

## Verdict: CLEAN NEGATIVE (confidence ~93%)

No divergences found. Every edge case tested matches solc 0.8.35 exactly, both
in value and in revert/Panic behavior.

## Why the core is faithful by construction

All word-level arithmetic in `SolidCore/Solidity/Shared/Word.lean` lifts directly
to the EvmYul `UInt256` opcode semantics (`div`, `sdiv`, `mod`, `smod`,
`addMod`, `mulMod`, `shiftLeft`, `shiftRight`, `sar`, `land/lor/xor/lnot`,
`signextend`). solc legacy codegen emits those same EVM opcodes, so raw-op
fidelity holds by construction. Divergence risk lives only in the Solidity-level
wrapping: checked-overflow detection points, type-cleanup routing, and
conversion width math. Those were the focus and all check out.

Key implementation sites reviewed:
- `Interpreter.lean:5469` `checkedExp` — overflow iff `wordModulus <= natPowCapped b e wordModulus` (saturating exp-by-squaring, O(log e)); wraps via `natPowMod`.
- `Interpreter.lean:5550` `checkedSignedExp` — sign-aware overflow: positive result overflows at `mag >= 2^255`, negative at `mag > 2^255` (INT_MIN = −2^255 allowed).
- `Interpreter.lean:5525` `checkedSignedDiv` — divByZero first, then checked `INT_MIN/-1` → overflow (Panic 0x11).
- `Interpreter.lean:5534` `checkedSignedMod` — divByZero only; `INT_MIN % -1` computed by `smodWord` (= 0, no revert).
- `Interpreter.lean:5570/5577` `checkedAddMod`/`checkedMulMod` — modulus==0 → divByZero (Panic 0x12); otherwise true 512-bit `addmodWord`/`mulmodWord` (no pre-wrap).
- `Interpreter.lean:633/659` `uintCast?`/`intCast?` — truncate low bits, int path sign-extends when `signBit <= low`.
- `Interpreter.lean:611` `fixedBytesCast?` — right-pad to target size (bytesN left-aligned).
- `Interface.lean:3412` `Ty.implicitCleanupCore?` — left shifts get a *truncating* `uintCast`/`intCast` (no overflow check even in checked mode); other checked ops get `uintCleanup`/`intCleanup`; `bytesN <<` re-masked to its lane.

## Evidence: solc vs solidity-lean (all match)

solc via Forge (pinned 0.8.35, optimizer off) / Lean `#eval` of the primitives:

| Case | solc 0.8.35 | solidity-lean | Match |
|---|---|---|---|
| `0**0`, `x**0`, `0**n` | 1, 1, 0 | 1, 1, 0 | ✓ |
| `2**256` (uint256, checked) | Panic 0x11 | Panic 0x11 | ✓ |
| `2**255` (uint256) | 2^255 | 2^255 | ✓ |
| `(-2)**3`, `(-2)**255`, `(-2)**256` (int256) | −8, −2^255, Panic 0x11 | −8, −2^255, Panic 0x11 | ✓ |
| `uint8(16)**2` / `uint8(15)**2` | revert / 225 | Panic 0x11 / 225 | ✓ |
| `int8(-2)**7` / `int8(-2)**8` | −128 / revert | −128 / Panic 0x11 | ✓ |
| `uint8(1)<<255`, `uint8(1)<<8` | 0, 0 | 0, 0 | ✓ |
| `1<<256` (uint256) | 0 | 0 | ✓ |
| `(-1)>>255`, `int8(-128)>>7` | −1, −1 | −1, −1 | ✓ |
| signed `>>256` (neg / pos) | −1 / 0 | −1 / 0 | ✓ |
| unsigned `>>256` | 0 | 0 | ✓ |
| `INT_MIN/-1` checked / unchecked | Panic 0x11 / INT_MIN | Panic 0x11 / INT_MIN | ✓ |
| `INT_MIN % -1` | 0 (no revert) | 0 (no revert) | ✓ |
| `-5/2`, `-5%3`, `5%-3` | −2, −2, 2 | −2, −2, 2 | ✓ |
| `x/0`, `x%0`, `mulmod(_,_,0)`, `addmod(_,_,0)` | Panic 0x12 | Panic 0x12 | ✓ |
| `addmod(2^256-1,1,5)` | 1 (true 2^256 mod 5) | 1 | ✓ |
| `mulmod(2^256-1,2^256-1,7)` | 1 | 1 | ✓ |
| `uint256(511)→uint8` | 255 | 255 | ✓ |
| `uint256(200)→int8` | −56 | −56 | ✓ |
| `int256(-1)→int8`, `int256(-1)→uint256` | −1, 2^256−1 | −1, 2^256−1 | ✓ |
| `bytes1(0xAB)→bytes32` | left-aligned (0xAB·2^248) | 0xAB·2^248 | ✓ |
| `-type(int).min` checked / unchecked | Panic 0x11 / INT_MIN | Panic 0x11 / INT_MIN | ✓ |

Forge probe (solc 0.8.35): `expU8_16_2` reverts, `expU8_15_2=225`,
`expI8_n2_7=-128`, `expI8_n2_8` reverts, `shlU8_1_255=0`, `shlU8_1_8=0`,
`addmod=1`, `mulmod=1`, `intminmod=0` — all reproduced by the Lean primitives.

## Notes on narrow-type checked exp (verified equivalent)

solc's `checkedExp` for a narrow result type (e.g. `uint8`) checks overflow at the
type's max during the loop; solidity-lean instead computes `checkedExp` against
the full 2^256 boundary and relies on the importer-inserted `uintCleanup`/
`intCleanup` (checked) around the result to enforce the narrow width. Both raise
Panic 0x11 at exactly the same inputs (confirmed: `uint8(16)**2` and
`int8(-2)**8` revert; `uint8(15)**2=225`, `int8(-2)**7=-128` succeed). No
observable difference.

## Residual (not divergences; would need the frontend/importer path)
- "Exponent must be unsigned" and "signed shift amount removed" are typechecker
  rejections, not value paths; not exercised here. The value engine treats the
  shift amount as the raw unsigned word (correct for 0.8.x — no masking to 2^n).

## Method
- Lean side: `lake env lean` `#eval` of `checkedExp`, `checkedSignedExp`,
  `checkedSignedDiv/Mod`, `checkedAddMod/MulMod`, `shlWord/shrWord/sarWord`,
  `uintCast?/intCast?`, `fixedBytesCast?`, `checkedSignedNeg` on exact words.
- solc side: scratch Foundry project, pinned solc-0.8.35, optimizer=false,
  via_ir=false, `staticcall` probes to observe revert vs value.
