# Sample Vault Walkthrough

This is a brainstorm document, not a specification. Its job is to stress the
target layer split by manually lowering one moderately rich Solidity contract
through every target language.

The sample is intentionally a little uncomfortable. It includes modifiers,
custom errors, events, mappings, checked arithmetic, payable entry, selector
dispatch, ABI encoding, storage layout, rollback, and an external value call.

## L00 SourceSolidity

```solidity
// Brainstorm sample, not intended as a verified fixture.
contract MiniVault {
    address public owner;
    uint256 public totalDeposits;
    bool public paused;
    mapping(address => uint256) public balances;

    error NotOwner(address caller);
    error Paused();
    error Insufficient(uint256 have, uint256 want);
    error TransferFailed();

    event Deposit(address indexed user, uint256 amount, uint256 newBalance);
    event Withdraw(address indexed user, uint256 amount, uint256 newBalance);

    modifier onlyOwner() {
        if (msg.sender != owner) revert NotOwner(msg.sender);
        _;
    }

    modifier whenLive() {
        if (paused) revert Paused();
        _;
    }

    constructor() {
        owner = msg.sender;
    }

    function setPaused(bool value) external onlyOwner {
        paused = value;
    }

    function deposit() external payable whenLive {
        uint256 newBalance = balances[msg.sender] + msg.value;
        balances[msg.sender] = newBalance;
        totalDeposits = totalDeposits + msg.value;
        emit Deposit(msg.sender, msg.value, newBalance);
    }

    function withdraw(uint256 amount) external whenLive {
        uint256 oldBalance = balances[msg.sender];
        if (oldBalance < amount) revert Insufficient(oldBalance, amount);

        uint256 newBalance = oldBalance - amount;
        balances[msg.sender] = newBalance;
        totalDeposits = totalDeposits - amount;
        emit Withdraw(msg.sender, amount, newBalance);

        (bool ok, ) = msg.sender.call{value: amount}("");
        if (!ok) revert TransferFailed();
    }
}
```

Relevant source behavior:

- Solidity 0.8-style arithmetic is checked unless explicitly unchecked.
- Modifier `_` preserves ordinary return, revert, and fallthrough behavior.
- Low-level `call` returns `false` on failure instead of automatically
  reverting.
- If `TransferFailed` is raised after storage writes and an event, all writes
  and logs in the current frame roll back.

## L01 ValidSolidity

`ValidSolidity` should be the resolved, typed, source-valid artifact. It should
not carry compiler layout facts.

```text
ContractId MiniVault

Storage identities:
  S_owner         : address                  declaration index 0
  S_totalDeposits : uint256                  declaration index 1
  S_paused        : bool                     declaration index 2
  S_balances      : mapping(address,uint256) declaration index 3

Errors:
  E_NotOwner(address)
  E_Paused()
  E_Insufficient(uint256,uint256)
  E_TransferFailed()

Events:
  Ev_Deposit(address indexed user, uint256 amount, uint256 newBalance)
  Ev_Withdraw(address indexed user, uint256 amount, uint256 newBalance)

Functions:
  F_setPaused(bool)   modifiers [M_onlyOwner]
  F_deposit()         modifiers [M_whenLive], payable
  F_withdraw(uint256) modifiers [M_whenLive]

Resolved source handles for withdraw:
  P_amount       : uint256 calldata argument 0
  L_oldBalance   : uint256 local
  L_newBalance   : uint256 local
  L_ok           : bool local
```

Validity facts that matter for later passes:

- `owner`, `totalDeposits`, `paused`, and `balances` are storage identities, not
  string lookups.
- `oldBalance`, `newBalance`, `ok`, and `amount` are unique local handles.
- `balances[msg.sender]` has type `uint256` and is a storage lvalue.
- `msg.sender.call{value: amount}("")` is an admitted external effect, not a
  pure expression.
- `deposit` is payable; `withdraw` and `setPaused` reject nonzero `msg.value`
  unless the chosen accepted subset says otherwise.

Immediate wart: storage layout facts are tempting to put here. This layer should
carry stable storage identities and enough declaration metadata to compute
layout later, but actual slot/hash/ABI layout belongs in
`AbstractYul -> GeneratedYul`.

Selectors, event topics, and error selectors are also not validity facts. They
belong in `AbstractYul -> GeneratedYul`.

## Pass Into L02 AbstractYul: Source-Language Lowering

There is no public desugared Solidity layer in the current target design. The
pass from `ValidSolidity` to `AbstractYul` handles source-language rewrites and
semantic lowering directly.

For intuition, modifier expansion has the same source meaning as:

```solidity
function setPaused(bool value) external {
    if (msg.sender != owner) revert NotOwner(msg.sender);
    paused = value;
}

function deposit() external payable {
    if (paused) revert Paused();

    uint256 newBalance = balances[msg.sender] + msg.value;
    balances[msg.sender] = newBalance;
    totalDeposits = totalDeposits + msg.value;
    emit Deposit(msg.sender, msg.value, newBalance);
}

function withdraw(uint256 amount) external {
    if (paused) revert Paused();

    uint256 oldBalance = balances[msg.sender];
    if (oldBalance < amount) revert Insufficient(oldBalance, amount);

    uint256 newBalance = oldBalance - amount;
    balances[msg.sender] = newBalance;
    totalDeposits = totalDeposits - amount;
    emit Withdraw(msg.sender, amount, newBalance);

    (bool ok, ) = msg.sender.call{value: amount}("");
    if (!ok) revert TransferFailed();
}
```

Lowering obligations:

- Expanding `whenLive` and `onlyOwner` must preserve return/revert/fallthrough.
- Expanded code must not accidentally capture locals from the function body.
- Any future modifier with code after `_` needs an explicit continuation story.

## L02 AbstractYul

`AbstractYul` is Yul-shaped control and generated local binding, but effects are
still typed and abstract. This is the first layer where source lexical structure
disappears.

One possible abstract program shape. Notice that this layer has typed external
entries, not concrete ABI selectors or calldata offsets:

```text
external entry F_setPaused(value : bool) =
  call setPaused(value)

external entry F_deposit() =
  call deposit()

external entry F_withdraw(amount : uint256) =
  call withdraw(amount)

proc requireLive() =
  let p := StorageRead(S_paused)
  if p then Revert(E_Paused, [])

proc requireOwner() =
  let sender := Env.msgSender
  let owner := StorageRead(S_owner)
  if sender != owner then Revert(E_NotOwner, [sender])

proc setPaused(value : bool) =
  call requireOwner()
  StorageWrite(S_paused, value)
  Return([])

proc deposit() =
  call requireLive()
  let sender := Env.msgSender
  let value := Env.msgValue
  let old := StorageRead(S_balances, [sender])
  let new := CheckedAdd(old, value)
  StorageWrite(S_balances, [sender], new)
  let total0 := StorageRead(S_totalDeposits)
  let total1 := CheckedAdd(total0, value)
  StorageWrite(S_totalDeposits, total1)
  Emit(Ev_Deposit, indexed := [sender], data := [value, new])
  Return([])

proc withdraw(amount : uint256) =
  call requireLive()
  let sender := Env.msgSender
  let old := StorageRead(S_balances, [sender])
  if old < amount then Revert(E_Insufficient, [old, amount])

  let new := CheckedSub(old, amount)
  StorageWrite(S_balances, [sender], new)
  let total0 := StorageRead(S_totalDeposits)
  let total1 := CheckedSub(total0, amount)
  StorageWrite(S_totalDeposits, total1)
  Emit(Ev_Withdraw, indexed := [sender], data := [amount, new])

  let ok := ExternalCallValue(
    target := sender,
    value := amount,
    calldata := empty,
    retBytes := 0)
  if not ok then Revert(E_TransferFailed, [])
  Return([])
```

The abstract effects here are typed:

- `StorageRead(S_balances, [sender])` is not yet a keccak slot formula.
- `Emit(Ev_Withdraw, ...)` is not yet `log2`.
- `Revert(E_Insufficient, ...)` is not yet bytes in memory.
- `ExternalCallValue` is a host/EVM relation assumption, not exact opcode
  behavior yet.
- External entries are still source function identities, not selector cases.

Wart exposed: `AbstractYul` needs a real answer for rollback. If effects update
state eagerly, then `Revert(E_TransferFailed, [])` after writes and logs must
restore the pre-call frame. Either the semantics needs transactional substate,
or effects need to produce a journal that commit/revert consumes.

## L03 GeneratedYul

`GeneratedYul` lowers layout, ABI, custom errors, events, mapping slots, and
selector dispatch into a concrete generated Yul subset.

Storage layout chosen for this sample:

```text
owner         slot 0
totalDeposits slot 1
paused        slot 2, encoded as 0 or 1
balances[a]   keccak256(pad32(a) ++ pad32(3))
```

Representative generated Yul:

```yul
{
  function balanceSlot(a) -> slot {
    mstore(0x00, a)
    mstore(0x20, 3)
    slot := keccak256(0x00, 0x40)
  }

  function revertPaused() {
    mstore(0x00, shl(224, 0x9e87fac8))
    revert(0x00, 0x04)
  }

  function revertInsufficient(have, want) {
    mstore(0x00, shl(224, 0xe8620800))
    mstore(0x04, have)
    mstore(0x24, want)
    revert(0x00, 0x44)
  }

  function revertTransferFailed() {
    mstore(0x00, shl(224, 0x90b8ec18))
    revert(0x00, 0x04)
  }

  function requireLive() {
    if iszero(iszero(sload(2))) { revertPaused() }
  }

  function withdraw() {
    requireLive()

    let amount := calldataload(0x04)
    let sender := caller()
    let bslot := balanceSlot(sender)
    let old := sload(bslot)
    if lt(old, amount) { revertInsufficient(old, amount) }

    let new := sub(old, amount)
    sstore(bslot, new)

    let total0 := sload(1)
    if lt(total0, amount) {
      // Panic(0x11) for arithmetic underflow; exact helper omitted here.
      revert(0x00, 0x24)
    }
    sstore(1, sub(total0, amount))

    mstore(0x00, amount)
    mstore(0x20, new)
    log2(
      0x00,
      0x40,
      0xf279e6a1f5e320cca91135676d9cb6e44ca8a08c0b88342bcdb1144f6511b568,
      sender)

    let ok := call(gas(), sender, amount, 0x00, 0x00, 0x00, 0x00)
    if iszero(ok) { revertTransferFailed() }
    return(0x00, 0x00)
  }

  if lt(calldatasize(), 4) { revert(0x00, 0x00) }
  switch shr(224, calldataload(0x00))
  case 0x16c38b3c { /* setPaused(bool) */ }
  case 0xd0e30db0 { /* deposit() */ }
  case 0x2e1a7d4d { withdraw() }
  default { revert(0x00, 0x00) }
}
```

Warts exposed:

- `AbstractYul -> GeneratedYul` is doing a lot: ABI, errors, events, storage
  layout, mapping hashing, selector dispatch, and external call ABI.
- `revert(0x00, 0x24)` for panic is a placeholder unless GeneratedYul has a
  real helper for Solidity panic encoding.
- Memory conventions need a small frame discipline so helpers do not overwrite
  live buffers unexpectedly.
- `call(gas(), ...)` pulls gas exactness into view. Early claims may need a
  gasless profile or a named gas-bound assumption.

## L04 StackCfg

StackCfg removes Yul lexical binding and helper functions. This sketch uses
symbolic stack names as proof annotations; the runtime artifact is still stack
positions.

```text
block dispatch.entry in []
  len := CALLDATASIZE
  if len < 4 -> revert.empty else dispatch.selector

block dispatch.selector in []
  selector := SHR(224, CALLDATALOAD(0))
  switch selector
    0x16c38b3c -> setPaused.entry
    0xd0e30db0 -> deposit.entry
    0x2e1a7d4d -> withdraw.entry
    default    -> revert.empty

block withdraw.entry in []
  amount := CALLDATALOAD(4)
  paused := SLOAD(2)
  if paused != 0 -> revert.paused else withdraw.loadBalance

block withdraw.loadBalance in [amount]
  sender := CALLER
  MSTORE(0x00, sender)
  MSTORE(0x20, 3)
  bslot := KECCAK256(0x00, 0x40)
  old := SLOAD(bslot)
  if old < amount -> revert.insufficient else withdraw.writeBalance

block withdraw.writeBalance in [amount, sender, bslot, old]
  new := SUB(old, amount)
  SSTORE(bslot, new)
  total0 := SLOAD(1)
  if total0 < amount -> revert.panicUnderflow else withdraw.writeTotal

block withdraw.writeTotal in [amount, sender, new, total0]
  total1 := SUB(total0, amount)
  SSTORE(1, total1)
  MSTORE(0x00, amount)
  MSTORE(0x20, new)
  LOG2(0x00, 0x40, TOPIC_Withdraw, sender)
  ok := CALL(GAS, sender, amount, 0x00, 0x00, 0x00, 0x00)
  if ok == 0 -> revert.transferFailed else return.empty

block return.empty in []
  RETURN(0x00, 0x00)
```

Wellformedness obligations this example needs:

- all labels closed and unique;
- every branch target has the advertised input stack shape;
- helper blocks such as `revert.insufficient` consume exactly the stack values
  they declare;
- max stack is below 1024;
- `DUP`/`SWAP` planning is valid after symbolic names are erased;
- pseudo operations such as `switch` and symbolic assignment are eliminated
  before bytecode.

Wart exposed: we may want an internal stack-planning notation with symbolic
names, even if the public `StackCfg` semantics is positional. Otherwise every
design discussion becomes unreadable `DUP`/`SWAP` soup too early.

## L05 Bytecode

The bytecode layer resolves labels, eliminates pseudo-instructions, computes
program counters, and emits bytes.

Readable opcode view, not exact bytes:

```text
pc_dispatch_entry:
  CALLDATASIZE
  PUSH1 0x04
  LT
  PUSH2 pc_revert_empty
  JUMPI

pc_dispatch_selector:
  PUSH1 0x00
  CALLDATALOAD
  PUSH1 0xe0
  SHR
  DUP1
  PUSH4 0x16c38b3c
  EQ
  PUSH2 pc_setPaused_entry
  JUMPI
  DUP1
  PUSH4 0xd0e30db0
  EQ
  PUSH2 pc_deposit_entry
  JUMPI
  DUP1
  PUSH4 0x2e1a7d4d
  EQ
  PUSH2 pc_withdraw_entry
  JUMPI
  PUSH2 pc_revert_empty
  JUMP

pc_withdraw_entry:
  JUMPDEST
  PUSH1 0x04
  CALLDATALOAD
  PUSH1 0x02
  SLOAD
  ISZERO
  ISZERO
  PUSH2 pc_revert_paused
  JUMPI
  ...
```

Bytecode proof obligations:

- every `PUSH2 pc_*` resolves to a real byte offset;
- every dynamic jump target lands on `JUMPDEST`;
- no jump targets point into PUSH immediate bytes;
- instruction lengths are stable after choosing PUSH widths;
- stack safety facts from `StackCfg` still hold for the concrete opcode stream;
- constructor/runtime code boundaries are explicit if constructor support enters
  the theorem.

## L06 Evm

The EVM theorem should talk about concrete execution of the runtime byte array.

Successful `withdraw(amount)` behavior:

```text
Initial frame:
  code     = MiniVault runtime bytecode
  calldata = 0x2e1a7d4d ++ abi_uint256(amount)
  caller   = A
  callvalue = 0
  storage[2] = 0
  storage[keccak256(pad32(A) ++ pad32(3))] = oldBalance
  storage[1] = totalDeposits
  oldBalance >= amount
  totalDeposits >= amount
  external call to A with value amount returns success

Final successful behavior:
  status = returned empty bytes
  storage[keccak256(pad32(A) ++ pad32(3))] = oldBalance - amount
  storage[1] = totalDeposits - amount
  log = Withdraw(A, amount, oldBalance - amount)
  external transfer subtrace includes CALL(to := A, value := amount)
```

Failure behaviors:

- if `paused != 0`, revert with `Paused()`;
- if `oldBalance < amount`, revert with `Insufficient(oldBalance, amount)`;
- if `totalDeposits < amount`, revert with Solidity panic underflow;
- if the external call returns failure, revert with `TransferFailed()`;
- in every reverting case, current-frame storage writes and logs are rolled
  back.

This is where gas, OOG, call depth, account existence, value-transfer failure,
and precompile behavior must either be modeled or excluded by profile
assumptions.

## Architecture Warts Surfaced

1. `ValidSolidity` needs real resolved source identities soon. The sample makes
   it obvious that string names are not enough for locals, storage, errors,
   events, functions, and modifiers.

2. Modifier expansion belongs in `ValidSolidity -> AbstractYul`, but modifiers
   with code after `_` will require a continuation-shaped proof, not naive text
   inlining.

3. `AbstractYul` must decide how rollback works. The `withdraw` function writes
   storage and emits a log before an external call that may cause a later revert.

4. Checked arithmetic should remain explicit until lowered. `old - amount` is
   guarded by the preceding branch, but `totalDeposits - amount` still needs a
   checked subtraction or an invariant proof.

5. `AbstractYul -> GeneratedYul` is the heavy middle pass. That is probably
   right, but it needs internal structure for ABI, storage layout, event/error
   encoding, memory discipline, and external calls.

6. `GeneratedYul` needs a generated-subset profile immediately. Otherwise this
   doc quietly drifts into arbitrary Yul support.

7. `StackCfg` probably needs a readable symbolic planning layer or annotation
   system, even if the checked artifact ultimately proves positional stack
   effects.

8. `Bytecode` must own PC arithmetic and `JUMPDEST` adequacy. That work should
   not leak upward into StackCfg or downward into the EVM model.

9. The EVM model cannot be just "bytecode step" forever. This sample needs
   frame rollback, logs, value transfer, host calls, gas/OOG policy, and
   account-world assumptions.

## Suggested Next Design Experiment

Before implementing the whole sample, choose one narrow slice:

```text
withdraw without external call and without event
```

Then add back, in order:

1. event emission and revert rollback;
2. external call success/failure;
3. exact custom error and panic encodings;
4. gas or an explicit gasless profile;
5. constructor/runtime packaging.

That sequence would test the layer boundaries without letting the hardest EVM
features swamp the first proof.
