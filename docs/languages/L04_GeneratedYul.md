# L04 GeneratedYul

## Purpose

`GeneratedYul` is the concrete Yul subset emitted by our compiler. It is not a
model of arbitrary user-written Yul.

One-line distinction from `AbstractYul`:

```text
Yul control and local binding, concrete Yul/EVM builtins.
```

## Language Shape

Expected constructs:

- Yul-style blocks, lets, assignments, ifs, switches, loops, and calls;
- only the subset of Yul constructs the compiler emits;
- concrete builtin operations such as `mload`, `mstore`, `calldataload`,
  `sload`, `sstore`, `keccak256`, `call`, `staticcall`, `delegatecall`, `logN`,
  `return`, and `revert` as they enter scope;
- generated helper functions or code blocks if the compiler emits them.

`switch`-based selector dispatch belongs here, because Solidity has no switch
and `AbstractYul` should not pretend to be concrete Yul.

## Semantics

The semantics should follow generated Yul execution over an EVM-like state:

- concrete memory, storage, calldata, returndata, logs, and call environment;
- Yul local scopes;
- concrete builtin behavior;
- structured control;
- returns/reverts as concrete byte-buffer exits.

It can be a restricted interpreter for the generated subset. It does not need to
accept arbitrary Yul.

## Wellformedness Boundary

This layer should own generated-subset facts:

- only supported generated constructs appear;
- generated names are fresh and scoped;
- helper labels/functions are closed;
- builtin usage matches the compiler profile;
- memory/storage/calldata conventions expected by the backend are present.

It should also name the semantic profile being used:

- exact builtins that are modeled directly;
- symbolic or relational builtins such as `keccak256` when exactness is not yet
  claimed;
- excluded host effects such as external calls or gas-sensitive behavior when
  the current slice does not cover them.

It should not own stack-depth or byte-offset facts. Those belong in `StackCfg`
and `Bytecode`.

## Outgoing Pass

`GeneratedYul -> StackCfg` lowers structured generated Yul into a stack-oriented
CFG.

The theorem should say that executing the CFG simulates or refines generated Yul
execution, preserving the observable EVM-relevant behavior.
