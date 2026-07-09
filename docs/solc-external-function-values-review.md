# External / public function-type values — solc vs solidity-lean review

Scope: first-class Solidity function values of **external/public** type
(`function() external`), distinct from internal function pointers (already
mined). Corpus pipeline: `optimizer=false`, no `--via-ir` ⇒ legacy codegen is
ground truth, but note that 0.8.35 ABI-decodes with the **mandatory ABI coder
v2** even on the legacy path (`CompilerUtils::abiDecode` dispatches to
`abiDecodeV2` whenever `useABICoderV2()`, which is always true ≥0.8.0), so the
Yul decode/validator functions in `ABIFunctions.cpp`/`YulUtilFunctions.cpp` are
the real decode semantics.

## Result: ZERO divergences found. Clean across every audited sub-surface.

### 1. On-stack / in-memory / ABI representation — LEFT-aligned 24 bytes
solc (`CompilerUtils::combineExternalFunctionType(true)`, and
`YulUtilFunctions::combineExternalFunctionIdFunction` = `shl64(or(shl32(addr),
and(selector,0xffffffff)))`): value is `addr<<96 | selector<<64`, i.e.
`address(20) ++ selector(4) ++ 8 zero bytes`, left-aligned in the word.
ABI-encoded (`storeInMemoryDynamic`, `encodeStaticValue?`) as those 24 bytes
right-padded to 32.

solidity-lean `encodeStaticValue?` (ABI.lean:172-179):
`wordToBytesBE 20 addr ++ wordToBytesBE 4 selector ++ replicate 8 0`. **Match.**

### 2. In-storage representation — RIGHT-aligned 24 bytes
solc (`combineExternalFunctionType(false)` / `splitExternalFunctionType(false)`,
LValue.cpp:255,339): store = `addr<<32 | selector` (bottom 24 bytes,
right-aligned). Read masks: `shr(32); and(2^160-1)` for address, `and(0xffffffff)`
for selector — so packed neighbours in the high 8 bytes of the slot cannot leak
into the address.

solidity-lean `externalFunctionStorageWord?` (Interpreter.lean:159-166) =
`addr*2^32 + selector`; `externalFunctionValueFromStorageWord`
(Interpreter.lean:170-174) = `addr := addressWord(word / 2^32)` (`addressWord`
masks `% 2^160`, Account.lean:26), `selector := word % 2^32`. The `/2^32` then
`%2^160` reproduces solc's `shr(32); and(2^160-1)` exactly, so packed dirty high
bytes are masked off identically. Storage packed width = 24 bytes
(Interface.lean:2223). **Match.**

### 3. ABI decode validation — only the trailing 8 bytes are checked
solc: `abi_decode_t_function_external` loads the full word then calls
`validator_revert_t_function_external`, whose condition is
`eq(value, cleanup_t_function_external(value))` and
`cleanup_t_function_external = cleanup_t_bytes24 =
and(value, 0xff..ff0000000000000000)` (top-24 mask). ⇒ reverts `revert(0,0)`
**iff** the low 8 bytes are non-zero. No range check on the address portion, no
selector check, no codesize check at decode time. (Confirmed by reading the
generated `--ir` for a `function() external` parameter.)

solidity-lean `abiDecode` external-function case (ABI.lean:355-367): reads
`address(0..20)`, `selector(20..24)`, `padding(24..32)`, and rejects (→ decode
failure) **iff** padding is non-zero. Same single check, same acceptance set.
**Match.**

### 4. `.address` / `.selector` members
solc split order is `(address, selector)`; `.selector` is `bytes4`
(left-aligned), `.address` is `address` (right-aligned). solidity-lean
(Interpreter.lean:6175-6188) returns `Value.word selector` / `Value.word addr`
from `Value.externalFunction addr selector`; `.selector` typed `bytes4` encodes
via `fixedBytes 4` = left-aligned (ABI.lean:166). Correct split order, correct
alignment. **Match.**

### 5. `==` / `!=`
Confirmed with the pinned binary that comparison **compiles** and the emitted
legacy bytecode masks each operand to 24 bytes and evaluates
`(a.addr==b.addr) && (a.sel==b.sel)`. solidity-lean (Interpreter.lean:5653-5673)
returns `wordEq lhsAddr rhsAddr && wordEq lhsSelector rhsSelector` for `eq` and
its negation for `ne`. **Match.**

### 6. Formation / call-through
`this.f`, `x.f`, storing/loading to storage & memory variables all funnel
through the same representation checked above (`externalFunctionValue` builder,
Interpreter.lean:6169-6174). Calling through a function value uses the stored
`address`+`selector` (Interface.lean:7143-7246); the extcodesize/codeless guard
is a separately-reviewed external-call concern (EO/CB/CS) and does not touch the
value representation.

## Evidence checked
- solc source: `CompilerUtils.cpp` {710-741 split/combine, 201-244 storeInMemory,
  246-268 abiDecode→v2}, `LValue.cpp` {255,339}, `ABIFunctions.cpp`
  {1393-1430 decode}, `YulUtilFunctions.cpp` {69-101 combine/split id, 3959-4057
  cleanup, 4059-4110 validator}.
- Pinned binary `solc-0.8.35`: `==` compiles + legacy bytecode inspected;
  `--ir` of a `function() external` parameter confirms cleanup/validator/split
  bodies (`cleanup_t_bytes24` mask `0xff..ff<8 zero bytes>`).
- solidity-lean: ABI.lean {102,166,172-179,355-367}, Interpreter.lean
  {156-174,5653-5673,6169-6188}, Interface.lean {2223,7143-7246}, Account.lean
  {24-27}.

Confidence: high. Clean negative.
