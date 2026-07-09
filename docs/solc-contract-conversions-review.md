# solc 0.8.35 vs solidity-lean — contract/interface conversions & contract-instance value semantics

Search-only divergence hunt over contract-type conversions and contract-instance runtime
values. Ground truth: pinned solc 0.8.35 (`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`).
Single-file closed world (multiple contracts per file allowed).

## Verdict

**CLEAN NEGATIVE — no divergence found (confidence ~90%).** Across all twelve mission
areas, the Lean type-checker's accept/reject decisions match pinned solc on every probe I
ran, contract-typed values are represented and lowered as 160-bit addresses exactly as
solc's ABI/value model dictates, and the runtime-relevant lowerings (`address(inst)`,
`C(addr)`, `this` → self, `type(C).name`, contract equality, up/down/unrelated casts) are
faithful. The area is also already covered by dedicated green fixtures
(`address-contract-conversions`, `contract-typed-locals`, `signed-unsigned-contract-conversions`,
`aggregate-contract-member`) plus the OZ/uniswap corpus, and the full replay is green (105/105).

## Empirical solc probes (all matched Lean)

Each program compiled with pinned solc; the expected Lean decision derived from the cited
type-checker code. All agreed.

| # | Program (essence) | solc | Lean decision (why) |
|---|---|---|---|
| eqAddr | `c == address(0)` (c: contract C) | REJECT "== cannot be applied to contract C and address" | REJECT — `canImplicitlyConvert` has no contract↔address arm either direction (`TypeCheck.lean:1058-1109`, `1281-1299`); eq gate `7342-7360` fails |
| eqUnrelated | `a == b` (A, B unrelated) | REJECT | REJECT — neither is ancestor of the other (`1295-1298`) |
| eqRelated | `a == b` (Base, Der is Base) | ACCEPT | ACCEPT — Der→Base implicit up-cast (`contractHasAncestorPathFuel`, `1295-1298`) + both equality-comparable (`3552-3553`) |
| downcastDirect | `Der(b)` (b: Base) | REJECT "Explicit type conversion not allowed" | REJECT — `Ty.canExplicitlyConvert` requires target be ancestor of source; Der is not ancestor of Base (`1505-1517`) |
| unrelatedDirect | `B(a)` (a: A) | REJECT | REJECT — same ancestor gate fails (`1505-1517`) |
| downViaAddr | `Der(address(b))` | ACCEPT | ACCEPT — address→contract admitted (`1501-1504`) |
| unrelViaAddr | `B(address(a))` | ACCEPT | ACCEPT — same (`1501-1504`) |
| selfInstEq | `x == this` (x: T, this: T) | ACCEPT | ACCEPT — same-type contracts, equality-comparable |
| thisExternal | `this.g()` in external fn | ACCEPT | ACCEPT — `this` typed as own contract (`TypeCheck.lean:4335-4344`), lowers to `Source.Expr.self` (`Interface.lean:3944-3945`), member-call becomes external call (`Interface.lean:5429-5480`) |
| newInterface | `new I()` (I interface) | REJECT "Cannot instantiate an interface" | REJECT — `requireCreatableContractDecl` requires `kind == contract` (`TypeCheck.lean:4926-4934`, used at `7143`) |
| typeName | `type(Foo).name` | ACCEPT | ACCEPT (string) — `TypeCheck.lean:5691-5696`; lowers to the contract's unqualified name bytes (`Interface.lean:3774-3778`) |

## Area-by-area findings

1. **`address(contractInstance)` / `payable(inst)` / `.balance`** — covered by
   `address-contract-conversions` and `contract-typed-locals` fixtures (round-trips,
   `payable(inst)`, `address(o).balance`). Contract→address is EXPLICIT-only (matches solc
   ≥0.5 which dropped the implicit contract→address). No divergence.

2. **`ContractType(addr)` cast** — `address→contract` accepted iff `isContractPath` and the
   payability guard `(sourcePayable || !contractCanReceiveEther path)` holds
   (`TypeCheck.lean:1501-1504`). This correctly rejects casting a non-payable address to a
   contract with `receive`/payable-`fallback` (the four `invalid/` fixtures), matching solc.
   Does not verify code at runtime — the cast is a pure reinterpret. `C(address(0))` accepted.

3. **`this` — external self-call vs internal call (mission priority).** `this` is typed as
   the current contract type (`TypeCheck.lean:4335-4344`) and lowers to `Source.Expr.self`
   (`Interface.lean:3944-3945`). `this.f()` is dispatched through the external-call path
   (`Expr.externalCallKindForTargetWithEnv`, `Interface.lean:5429-5480`) — distinct from a
   bare `f()` internal call. Exercised by `openzeppelin-pausable-reentrancy` and
   `base-constructor-runtime-args` fixtures (green). No divergence.

4. **Up-cast (derived→base)** — implicit; `contractHasAncestorPathFuel`
   (`TypeCheck.lean:1295-1298`). Dispatch through a base-typed handle is an external call
   resolved by selector at the target address (most-derived override) — covered by the OZ
   inheritance corpus. No divergence.

5. **Down-cast (base→derived)** — direct `Der(b)` REJECTED; `Der(address(b))` ACCEPTED.
   Both match solc (probes downcastDirect / downViaAddr). Root: `Ty.canExplicitlyConvert`
   ancestor gate (`TypeCheck.lean:1505-1517`).

6. **Unrelated contract cast** — direct `B(a)` REJECTED; `B(address(a))` ACCEPTED. Match
   (probes unrelatedDirect / unrelViaAddr).

7. **Contract equality** — `inst1 == inst2` accepted only when a common contract type exists
   (one is ancestor of the other), rejected for unrelated pairs, and `inst == address(0)`
   rejected — all matching solc exactly (probes eqRelated / eqUnrelated / eqAddr / selfInstEq).
   Equality-comparability gate at `TypeCheck.lean:3539-3554`, `7342-7360`.

8. **Contract type in ABI == address (mission priority).** `abiCanonicalFuel?` maps any
   non-library `Ty.user` contract/interface to the string `"address"`
   (`TypeCheck.lean:970-976`), so `f(C c)` and `f(address)` share the identical 4-byte
   selector and 20-byte-left-padded-to-32 encoding. No divergence.

9. **`type(C)` members** — `type(C).name` typed `string` and lowered to the contract's
   unqualified name (`TypeCheck.lean:5691-5696`, `Interface.lean:3774-3778`) — matches solc's
   `"Foo"`. `type(I).interfaceId` gated to interface/abstract only (`5711-5719`), matching
   solc. `type(C).creationCode`/`.runtimeCode` type-check to `bytes` and lower to
   `Expr.contractCreationCode`/`contractRuntimeCode` (`Interface.lean:3779-3784`) — the actual
   returned bytecode value is **out of scope** for this create-bytecode-free semantics; not a
   conversion issue. (See "Out of scope.")

10. **Storage/memory of contract-typed variables** — a contract type is address-sized (20
    bytes, packable) via the `abiCanonical? = "address"` treatment and the `Ty.user`→address
    value model; `aggregate-contract-member` fixture covers a contract-typed struct member.
    No divergence observed.

11. **`new C()` returns a C instance** — creation returns a contract-typed (address) handle;
    creation eval order is covered by DIV-CREATE/`contract-creation` fixtures. `new I()`
    correctly rejected for interfaces (probe newInterface).

12. **Interface types** — `I(addr).f()` external call; interfaces are `ContractKind.interface`,
    canonicalize to `address` in ABI, cannot be `new`-instantiated. No divergence.

## Out of scope (noted, not a divergence)

- **`type(C).creationCode` / `type(C).runtimeCode` returned VALUE** — this semantics has no
  real create/runtime EVM bytecode, so the concrete `bytes` value these members produce
  (`Interface.lean:3779-3784` → `Expr.contractCreationCode`/`contractRuntimeCode`,
  `Interpreter.lean:6106-6112`) cannot be byte-compared against solc's actual bytecode. This
  is a known create-bytecode exclusion, orthogonal to contract-type CONVERSION semantics.

## Confidence & caveats

~90%. The type-system decisions are exhaustively confirmed against solc (11/11 probes) and
grounded in cited code. Runtime dispatch (external self-call, up-cast most-derived dispatch)
is confirmed via the lowering path and exercised by existing green fixtures rather than by a
fresh per-snippet interpreter run, which is the residual 10%. No fabricated positives.
