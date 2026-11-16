# Second held-out draw: result (H4, H5)

Drawn by `draw.py` exactly as frozen in `PROCEDURE.md` (published first, in solidity-lean
7f7230f7f0d67ac650d5771e4d7248839409ff2f), with seed
`4758becf4ea3dc5ccb0ed92b8d3e17aa2573bcbb810ec04acbd19d6741adc96e`. The full output is `draw.json`:
152 candidates, 23 excluded by the fixed rules, 116 outside the envelope, 2 with no contract at all
(`enum/EnumDeclaration.sol`, `structs/StructDeclaration.sol`: file-level declarations only; the
script records them as `KeyError: 'contracts'`, and both rank after H5, so they cannot change the
draw), and 11 eligible. Ranked:

1. **H4** `contracts/src/function-modifier/FunctionModifier.sol` (contract `FunctionModifier`)
2. **H5** `contracts/src/error/Account.sol` (contract `Account`)
3. ether-units/EtherUnits, primitives/Primitives, bitwise/MostSignificantBitFunction, enum/Enum,
   array/ArrayReplaceFromEnd, if-else/IfElse, constants/Constants, unchecked-math/UncheckedMath,
   events/Events (not drawn).

H4 is a contract the first selection had left out by judgment (recursion). Under this rule it
stays: nothing is replaced. H5 is held until a runner is free.

## Specs (written after the draw, before any run)

Only `@custom:` lines added; removing every line containing `@custom:` gives the upstream file byte
for byte (`upstream/`). Getters the compiler generates carry no spec.

- **H4 FunctionModifier** (`owner` set to the deployer in the constructor; `x = 10`):
  - `changeOwner(address)`: succeeds if `msg.value == 0 && msg.sender == owner && _newOwner !=
    address(0)`; ensures `owner == _newOwner`.
  - `decrement(uint256)`: `noReentrancy` sets `locked` before the body, so the recursive call for
    `i > 1` always reverts. It succeeds if `msg.value == 0 && !locked && i <= 1 && i <= x`;
    ensures `x == old(x) - i && !locked`.
- **H5 Account** (`MAX_UINT` is a constant):
  - `deposit(uint256)`: `balance + _amount` is checked, so it succeeds if `msg.value == 0 &&
    balance + _amount <= type(uint256).max`; ensures `balance == old(balance) + _amount`.
  - `withdraw(uint256)`: succeeds if `msg.value == 0 && _amount <= balance`; ensures
    `balance == old(balance) - _amount`.

## How to run

As for H1-H3: one driver run per case at solar 800d78a9, base 44572c15, default tier, NatSpec
spec, `--contract` as named. If CERTIFIED, an exact fresh-clone replay on the same sha; whatever it
exits is its verdict, and RC.md reports it.

| Case | Source | `--contract` |
|---|---|---|
| H4 | `tests/heldout/rc-2026-11-15/draw2/H4-FunctionModifier/FunctionModifier.sol` | `FunctionModifier` |
| H5 | `tests/heldout/rc-2026-11-15/draw2/H5-Account/Account.sol` | `Account` |
