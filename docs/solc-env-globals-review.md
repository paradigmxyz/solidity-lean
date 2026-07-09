# solc env / global-builtins divergence review (semantic content only)

Scope: derived / rule-bearing global builtins in solidity-lean vs pinned solc 0.8.35
(legacy codegen). Search-only; no Lean semantics changed. Raw gas metering and
create-bytecode surfaces are treated as intentional exclusions (noted below).

Ground truth: solc `0.8.35+commit.47b9dedd`, executed via anvil + cast (Foundry
1.5.1). Each empirical result below was reproduced against a live EVM.

## Verdict: CLEAN. No divergences found across the examined semantic surfaces.

Every rule-bearing predicate examined matches solc / the EVM spec. Details and
evidence per surface follow. Confidence is stated per item.

---

### 1. msg.sig / msg.data (short-calldata / fallback)  — CLEAN, 98%

Lean derives `msg.sig` from the *calldata*, not the dispatched selector:
- `Expr.msgSig => Value.word (calldataSelectorWord context.calldata)`
  (`SolidCore/Solidity/Interpreter.lean:6112`)
- `calldataSelectorWord c = bytesToWordBE (bytesPrefixRightPadded 4 c)`
  (`Interpreter.lean:56`) — first 4 bytes, **right-padded** with zeros.
- `msg.data` = full calldata (`Expr.calldata`, `Interpreter.lean:6110`).

The mission brief's premise that `msg.sig == 0x00000000` for <4-byte calldata is
**incorrect**; solc right-pads (matches the EVM `calldataload(0) >> 224`
lowering). Empirically confirmed against solc 0.8.35 in a `fallback`:

| calldata      | solc msg.sig | solc msg.data.length | Lean (right-padded) |
|---------------|--------------|----------------------|---------------------|
| `0xAABB`      | `0xaabb0000` | 2                    | `0xaabb0000` ✓      |
| `0xAA`        | `0xaa000000` | 1                    | `0xaa000000` ✓      |
| `0x` (empty)  | `0x00000000` | 0                    | `0x00000000` ✓      |
| `0xAABBCCDDEEFF` | `0xaabbccdd` | 6                 | `0xaabbccdd` ✓      |

Lean matches solc exactly, including the sub-4-byte cases. Only genuinely-empty
calldata yields `0x00000000`.

Side confirmation: `msg.data` inside `receive()` is a TypeError in solc 0.8.35
(compile error on `msg.data.length`), which matches Lean witness G10
(`SolidCore/Witness/AcceptanceBoundaries.lean:331-360`; typecheck guard
`TypeCheck.lean:5406` `require (!(member == "data" && env.inReceive))`).

### 2. blockhash(uint) window  — CLEAN, 97%

`blockhashNumberInRange current requested = requested < current && current - requested <= 256`
(`SolidCore/Solidity/Shared/Block.lean:83-86`); out-of-window → `bytes32(0)`
(`blockHashAt`, `Block.lean:88-93`). This is exactly the EVM BLOCKHASH window
`block.number-256 <= n <= block.number-1` (current excluded, >256-old excluded,
future excluded). No off-by-one. The in-window value itself is oracle-seeded
(`blockHashes` map), matched by construction.

### 3. block.prevrandao / block.difficulty  — CLEAN, 95%

Both `block.difficulty` and `block.prevrandao` parse and are typed `uint256`
(`Interface.lean:4303,4312,5058,5061`). Both lower to the *same* opcode-0x44
read, gated on EVM version: `evmVersion.parisOrLater` → reads the `prevrandao`
env field; otherwise → `difficulty` field
(`Interpreter.lean:1915-1921` and `1928-1934`). This matches post-merge EVM
semantics (0.8.18+ rename; DIFFICULTY became PREVRANDAO). Witnesses
`environmentDifficultyAliasesPrevrandao` / `environmentPreParisPrevrandaoUsesDifficulty`
(`Interface.lean:3297-3316`) pin both branches. Other block globals typed
correctly (all uint256; coinbase address payable).

### 4. type(intN/uintN).min / .max  — CLEAN, 99%

`Ty.typeInfoExpr?` (`Interface.lean:3724-3743`):
- uintN: min `0`, max `2^bits - 1`.
- intN: min = two's-complement word `2^(bits-1)` (i.e. −2^(bits-1)),
  max = `2^(bits-1) - 1`.
Exact two's-complement bounds (e.g. int8 → 0x80 / 127). Correct.

### 5. type(I).interfaceId (inheritance)  — CLEAN, 95%

`ContractDecl.interfaceId?` (`Interface.lean:18221-18233`) XORs the selectors of
`directOrdinaryFunctions` filtered to `isInterfaceFunction`, plus public-state-var
getter selectors; it does **not** include inherited functions. This matches
solc's documented rule ("XOR of all function selectors defined within the
interface itself — excluding inherited functions").

Empirically confirmed with `interface I is J`:
- `selector(foo)=0xc2985578`, `selector(bar)=0xfebb0f7e`
- solc `type(J).interfaceId = 0xfebb0f7e` (= bar)
- solc `type(I).interfaceId = 0xc2985578` (= foo **only**, NOT foo⊕bar)

Lean's use of `directOrdinaryFunctions` reproduces the inherited-exclusion; no
double-counting and no missing-selector bug.

### 6. ecrecover / precompiles  — CLEAN by construction, 85% (oracle-driven)

`ecrecover`/`sha256`/`ripemd160` are modeled as ordinary precompile
STATICCALLs answered by the open-world responder
(`Interpreter.lean:2352` emit path; `Shared/Precompile.lean`), not by a Lean-side
arithmetic predicate. The `address(0)`-on-invalid-signature (no revert) behavior
is therefore whatever the oracle/EVM returns, matched by construction rather than
re-derived. No divergence surface in the Lean rules; flagged as oracle-boundary
rather than semantic-predicate.

### 4b/misc. address members  — CLEAN / oracle-driven

- `.balance` reads dynamic self balance (A2) or the seeded `accountBalances`
  map (`envAccountBalance`, `Interpreter.lean:2215`).
- `.codehash` = `codehashAt` seed map, default 0 for accounts absent from the map
  (EIP-1052 nonexistent→0, `Interpreter.lean:2246-2259`). The existing-empty-code
  case (keccak256("")=0xc5d246...) vs nonexistent (0) distinction lives in the
  oracle seed, not in a Lean predicate — matched by construction.

---

## Surfaces judged OUT OF SCOPE (noted, not divergences)

- **Raw gas**: `gasleft()` (modeled as resource query `emitGasleft`,
  `Interpreter.lean:6123`), send/transfer 2300 stipend — intentional gas
  exclusion. (Boolean-return-vs-revert for send/transfer was not separately
  stress-tested here.)
- **Create-bytecode**: `type(C).creationCode` / `.runtimeCode` /
  `<address>.code` — sourced from `namedBytesAt` / oracle
  (`Interpreter.lean:6098-6111`); create-bytecode is an excluded surface.
- **ecrecover/sha256/ripemd160 numeric results**: oracle-answered precompiles,
  not Lean predicates (see §6).

## Method notes

solc runtime behavior reproduced with the pinned `solc-0.8.35` binary compiled to
bytecode and executed on anvil via `cast send`/`cast call`; Lean predicates read
directly from source. The `/Users/dan/.local/bin/solc` on PATH is 0.8.26 and must
NOT be used for 0.8.35 pins — the artifact binary
`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35` is authoritative.
