# solidity-lean vs solc 0.8.35 — `abi.encodeCall` selector derivation review

Surface reviewed: `abi.encodeCall` / `encodeWithSelector` / `encodeWithSignature`
(selector derivation + argument encoding), plus a spot-check of `delete` on
aggregates and array `.push()`/`.pop()` (both found clean — see notes at end).

Ground truth: pinned `/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`.

---

## CONFIRMED — wrong-value: `abi.encodeCall` derives the 4-byte selector from the ARGUMENT types, not the callee's declared PARAMETER types

### Classification
wrong-value. Confidence: high (both solc and the solidity-lean source traced).

### Root cause (solidity-lean)
`Expr.functionPointerSelectorCore?`, `SolidCore/Solidity/Interface.lean:5091`.
For a member function pointer (`X.f`, `i.f`, `this.f`) the `Expr.member _ name`
branch (lines 5093–5104) builds the signature from the **argument** type list it
is handed:

```
let signature ← externalFunctionSignature? name argTys      -- Interface.lean:5101
```

`argTys` is the list of *source argument* types produced by
`TupleItems.toAbiEncodeSource?` / `Expr.toAbiEncodeSourceArg?` at the two
`encodeCall` call sites (`Interface.lean:4209-4229`). `externalFunctionSignature?`
(`Interface.lean:3695`) just joins those canonical names into `name(a,b,...)` and
`selectorFromSignature` hashes it. The callee's real parameter types are never
consulted here, even though TypeCheck already resolves them
(`functionPointerSig?`, `TypeCheck.lean:4644`).

solc always derives the `encodeCall` selector (and the encoding) from the
**declared parameter types** of the referenced function, and separately checks
that each argument is *implicitly convertible* to its parameter type.

TypeCheck accepts the argument list whenever each arg is assignable to the
declared param (`checkCheckedExprsAssignableTo`, `TypeCheck.lean:4487`, via
`expectAssignableToIn`), so these programs are **accepted and evaluated** — the
divergence is a wrong return value, not an over-reject.

Because number literals are typed `uint256` by `Literal.abiTy?`
(`Interface.lean:3560`) and small integer variables keep their narrow type, the
solidity-lean signature disagrees with solc's whenever an argument's static type
differs from the parameter type by an implicit conversion. (For scalar
widening/sign-extension the *encoded value bytes* still coincide — both pad to 32
bytes — so the **selector** is the observable divergence.)

### Repro A — argument narrower than parameter
```solidity
// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;
interface I { function foo(uint256 x) external; }
contract C {
  function g(I i) public pure returns (bytes memory) {
    uint8 y = 3;
    return abi.encodeCall(i.foo, (y));   // arg uint8, param uint256
  }
}
```
solc: selector = `foo(uint256)` = `0x2fbebd38`
(`--ir`: `expr_..._functionSelector := 0x2fbebd38`; cross-checked against
`I.foo.selector`).
solidity-lean: `argTys = [uint8]` ⇒ `externalFunctionSignature? "foo" [uint8]`
= `"foo(uint8)"` ⇒ selector `0x11602fb3`. **Wrong first 4 bytes of the result.**

### Repro B — literal narrower than parameter (more common)
```solidity
// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;
contract C {
  function foo(uint8 x) external {}
  function g() public view returns (bytes memory) {
    return abi.encodeCall(this.foo, (3));   // literal 3, param uint8
  }
}
```
solc: selector = `foo(uint8)` = `0x11602fb3` (confirmed in `--ir` and in the
deployed runtime bytecode: `...6311602fb36003...`).
solidity-lean: literal `3` ⇒ `Literal.abiTy?` = `uint256` ⇒ signature `foo(uint256)`
⇒ selector `0x2fbebd38`. **Wrong.**

Both directions therefore diverge; the two repros bracket the bug.

### Why the frozen corpus missed it
The overwhelmingly common `encodeCall` usage writes arguments whose static types
already equal the parameter types (`encodeCall(C.f, (exactTypedArg))`), for which
`argTys == paramTys` and the selector happens to be right. The gap only opens on
an implicit-conversion argument (narrow variable, or an integer literal against a
non-`uint256` parameter), which the corpus evidently never exercised.

### Latent secondary effect (not independently observable today)
The *encoding* types `coreTys` are likewise taken from the arguments, not the
parameters (same call sites). For every implicit conversion solc actually permits
here (scalar widening / literal→intN / sign-extension) the 32-byte-padded output
bytes coincide, so this is not separately observable now — but it is the same
root defect and would surface if any non-scalar implicit conversion were ever
admitted on this path.

### Suggested fix direction (for the fix loop, not applied here)
In the `Expr.member _ name` branch of `functionPointerSelectorCore?`, resolve the
referenced function's declared parameter types (TypeCheck already has them via
`functionPointerSig?`) and build both the selector signature and the encode
`coreTys` from those parameter types, not from `argTys`.

---

## Surfaces spot-checked and found CLEAN (no divergence)

- **`delete` on aggregates** (`Runtime.deleteStorageField/Index/Path`,
  `Interpreter.lean:3893-4136`; `State.clearStorageLayoutAtFuel`,
  `:3627-3697`): dynamic array clears every data slot then zeroes the length
  slot; `bytes`/`string` clear via `storeStorageBytesAt … []`; mapping is a
  no-op; nested struct / struct-with-mapping recurse with fuel = `clearDepth`
  and skip mapping members. Matches solc `clear_storage_range` behavior.
- **array `.push()` / `.pop()`** (`Runtime.storageArrayPush/Pop`,
  `Interpreter.lean:4273-4382`): no-arg `push()` clears the new tail slot then
  bumps length; valued push deep-clears then writes; `pop` deep-clears the
  vacated slot then decrements; pop-on-empty panics (`popEmptyArray`); length
  overflow guarded. Matches solc.
