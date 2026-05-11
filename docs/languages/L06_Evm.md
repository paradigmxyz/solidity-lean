# L06 Evm

## Purpose

`Evm` is the declared target semantics. It should model the EVM accurately
enough for the verified compiler claim and should not be shaped around compiler
convenience.

Forge parity tests are evidence for this layer. Lean theorem statements are the
verification boundary.

## Change From Previous Layer

Compared with `Bytecode`, this layer adds the actual EVM execution environment:

- account/world state;
- call frames;
- gas and OOG behavior when claimed;
- memory expansion;
- value transfer;
- returndata;
- logs;
- call/create/selfdestruct/precompile behavior as supported;
- deployment/initcode/runtime distinction when supported.

The transition from `Bytecode` to `Evm` is embedding and adequacy, not normal
compiler lowering.

## Basic Syntax

The target language is EVM bytecode running in an EVM state:

```text
World:
  accounts
  balances
  storage
  code
  nonce

Frame:
  pc
  code
  stack
  memory
  calldata
  returndata
  caller
  address
  callvalue
  gas
  static flag

Outcome:
  running
  return(bytes)
  revert(bytes)
  stop
  invalid/stuck
  outOfGas
```

The exact state can grow with the verified profile, but exclusions must be
visible.

## Semantics

The semantics should be the public target relation used by final compiler
theorems:

- opcode execution;
- stack/memory/storage effects;
- return/revert/stop/failure behavior;
- gas and memory expansion when included in the claim;
- calls and account-world effects when included;
- logs and observable traces;
- deployment behavior when constructors/initcode are claimed.

Invalid/stuck/OOG behavior should not disappear. Either the final theorem proves
compiled code avoids those outcomes under hypotheses, or the outcomes appear in
the target behavior.

## Incoming Pass: Bytecode -> Evm

This is target embedding.

Transformations and packaging:

- install runtime bytecode as account code;
- choose initial call frame;
- provide calldata and callvalue;
- provide initial world/storage/account state;
- provide gas assumptions or gasless profile assumptions;
- provide external call/precompile/host relations;
- connect bytecode artifact `WF` to EVM safety obligations.

The theorem should say:

```text
Bytecode.WF code
and environment assumptions
imply EVM execution of code refines Bytecode behavior.
```

For early theorems, acceptable restrictions include:

- already-deployed runtime code only;
- gasless or sufficient-gas execution;
- single-contract world;
- no external calls;
- no constructors;
- no dynamic calldata/returndata.

Those restrictions must be theorem hypotheses or profile predicates, not prose.

## Final Theorem Role

The final public compiler theorem should reach this layer:

```text
SourceSolidity source
  -- check -->
ValidSolidity valid
  -- lower -->
AbstractYul abstract
  -- generate -->
GeneratedYul yul
  -- stack lower -->
StackCfg cfg
  -- assemble -->
Bytecode code
  -- embed/run -->
Evm behavior
```

Stopping at bytecode, generated Yul, or a proof adapter is not the final target
claim unless an explicit adequacy theorem connects it to this semantics.
