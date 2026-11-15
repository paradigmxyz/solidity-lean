# Uniswap V2 port: function specifications for review

Lean statements for every external function of the pinned 0.8 port's `UniswapV2ERC20`,
`UniswapV2Pair` and `UniswapV2Factory` (getters and constructors excepted, see W8), in
`Contracts/UniswapV2/Specs/` (`lake build ContractsUniswapV2Specs`). **Statements only**: the
files hold definitions and `Prop`s, no proofs and no `sorry`. Nothing here proves or claims
any edge of [CERTIFICATION_TARGET.md](../CERTIFICATION_TARGET.md); each `…Spec` is a candidate
for E7 once its model is connected to SolidCore's runs.

The specifications are written from the port's behaviour, not generated from it: no port source
is in the repository. They follow the certified transfer slice
(`Contracts/UniswapV2/ERC20/Slice/Post.lean`):

- **`…Result`, the sequential model**: the source's steps in source order (reads, SafeMath,
  writes, logs, external requests, reverts), each read seeing the writes before it. Exact for
  every storage and every world answer; needs no hash premise.
- **`…Target`, the target statement**: the key properties in the words of the storage before
  the call and the world's answers, key by key.
- **`…Spec`, the statement to prove**: on every valid call whose premises hold, the model meets
  the target. `Specs.AllSpecs` (All.lean) is their conjunction.

Reviewers: the statements to read are the `…Target`s and the premises of each `…Spec`. The
`…Result` models are the reference behaviour the targets summarise.

## The model of a call (Common.lean)

| Lean | Meaning |
|---|---|
| `Env` | `msg.sender`, `address(this)`, `block.timestamp`, `block.chainid`, `msg.value` |
| `Store`, `Words st` | storage as a word per slot, indexed modulo 2^256 |
| `World` | `ans i req`: the answer to the call's i-th external request; `hasCode`; `ecrecover` |
| `Result` | success, output, logs, storage (as `SolarTV.Observable`) and the requests made, in order |
| `add`, `sub`, `mul` | SafeMath: revert with `ds-math-add-overflow` / `-sub-underflow` / `-mul-overflow` |
| `div`, `inc` | checked `/` (Panic 0x12) and `x++` (Panic 0x11) |
| `callWord`, `callAddress` | high-level call with a return value: a failure bubbles the callee's revert data; short or out-of-range return data reverts with no data |
| `callUnit` | high-level call with no return value: no code at the target reverts with no data first |
| `safeTransfer` | the pair's `_safeTransfer`: empty return or `true` passes; failure or `false` is `UniswapV2: TRANSFER_FAILED`; other return data reverts with no data |
| `ScopedSep L` | `SolidCore.Spec.ScopedSep`: keccak256 injective with images ≥ 2^128 on the finite footprint `L` only |

## UniswapV2ERC20 (ERC20.lean)

Slots: `totalSupply` 0, `balanceOf` 1, `allowance` 2, `DOMAIN_SEPARATOR` 3, `nonces` 4.

| Function | Lean | Statement in plain English | Premises |
|---|---|---|---|
| transfer | `ERC20.TransferSpec` / `TransferTarget` / `transferResult` | Already certified at caller 0x2000 (`Slice.TargetPost`); restated here for any caller, unchanged: caller ≠ to succeeds iff the caller's balance covers value and to's balance + value < 2^256, then debit and credit; caller = to succeeds iff the balance covers value, storage unchanged; success logs `Transfer(caller, to, value)`, returns true, writes nothing outside the two balance slots; failure reverts with the SafeMath message and changes nothing. | P2, P3, `ScopedSep (transferFootprint caller to)` |
| approve | `ERC20.ApproveSpec` / `ApproveTarget` | Always succeeds; storage is exactly the old storage with `allowance[caller][spender] = value`; logs `Approval(caller, spender, value)`; returns true. | P2, P3; no hash premise (stated at the slot) |
| transferFrom | `ERC20.TransferFromSpec` / `TransferFromTarget` | With a = allowance[from][caller], b = balanceOf[from], d = balanceOf[to] before the call: succeeds iff (a = max or value ≤ a) and value ≤ b and (from = to or d + value < 2^256). A finite allowance drops by value, an infinite one stays. from ≠ to debits and credits; from = to leaves the balance. Logs `Transfer(from, to, value)`, returns true, writes nothing else. Failure: `ds-math-sub-underflow` (allowance, then balance) or `ds-math-add-overflow`; no change. | P2, P3, `ScopedSep (HashScopeNested.transferFromFootprint caller from to)` |
| permit | `ERC20.PermitSpec` / `PermitTarget` | With n = nonces[owner] and signer = ecrecover(EIP-712 digest of the stored DOMAIN_SEPARATOR and (owner, spender, value, n, deadline), v, r, s): succeeds iff timestamp ≤ deadline, n < 2^256 − 1 and signer = owner ≠ 0. Then nonces[owner] = n + 1, allowance[owner][spender] = value, nothing else; logs `Approval(owner, spender, value)`; no return data. Failure order: `UniswapV2: EXPIRED`, Panic 0x11, `UniswapV2: INVALID_SIGNATURE`; no change. | P2, P3, P7, `ScopedSep (permitFootprint owner spender)` (nonces[owner], allowance[owner][spender]), v < 256 |

## UniswapV2Pair (Pair.lean)

Slots: ERC20's 0–4, `factory` 5, `token0` 6, `token1` 7, `reserve0 | reserve1 | blockTimestampLast` packed in 8, `price0CumulativeLast` 9, `price1CumulativeLast` 10, `kLast` 11, `unlocked` 12.

Shared steps: `lock` (`UniswapV2: LOCKED` unless unlocked = 1; 0 during the body, 1 after), `update` / `updateStore` (`_update`: both balances < 2^112 or `UniswapV2: OVERFLOW`; cumulative prices grow by `(r_other · 2^112 / r) · elapsed` mod 2^256 when elapsed and both old reserves are nonzero; reserves := (b0, b1, timestamp mod 2^32); `Sync(b0, b1)`), `mintFee` / `feeLiquidity` (`_mintFee`: ask the factory's `feeTo()`; fee on iff nonzero; mint `totalSupply · (√k − √kLast) / (5√k + √kLast)` to feeTo when kLast ≠ 0 and √k grew; fee off clears kLast).

| Function | Lean | Statement in plain English | Premises |
|---|---|---|---|
| initialize | `Pair.InitializeSpec` / `InitializeTarget` | Succeeds iff the caller is `factory`; then token0 and token1 hold the arguments (upper 96 bits of their slots kept), nothing else changes, no log, no return data; otherwise `UniswapV2: FORBIDDEN`. Not locked and not once-only (as the source). | P2, P3 |
| getReserves | `Pair.GetReservesSpec` / `GetReservesTarget` | Always succeeds; returns reserve0, reserve1, blockTimestampLast from slot 8; changes nothing. | P3 |
| sync | `Pair.SyncSpec` / `SyncTarget` | Locked → `LOCKED`. Otherwise asks token0 then token1 for the pair's balance; succeeds iff both answer a word and both are < 2^112; then storage is exactly `updateStore` with those balances (reserves = balances, timestamp, prices); logs `Sync(b0, b1)`. | P1, P2, P3, P8 |
| skim | `Pair.SkimSpec` / `SkimTarget` | Locked → `LOCKED`. A success asked token0's balance b0 ≥ reserve0, sent b0 − reserve0 of token0 to `to`, then the same for token1 (four requests, both transfers accepted); storage unchanged, no log, no return data. A balance below its reserve reverts with `ds-math-sub-underflow`. | P1, P2, P3 |
| mint | `Pair.MintSpec` / `MintTarget` | Locked → `LOCKED`; a balance below its reserve → `ds-math-sub-underflow`. A success, with a0 = b0 − r0, a1 = b1 − r1, fee = protocol fee for the factory's feeTo answer and T = totalSupply + fee: requests are balanceOf(token0), balanceOf(token1), feeTo(); liquidity = √(a0·a1) − 1000 when T = 0 (1000 more minted to address 0), else min(a0·T/r0, a1·T/r1); liquidity > 0 and returned; balanceOf[to] grows by liquidity (plus fee when to = feeTo, plus 1000 when to = 0 and T = 0); totalSupply grows by fee + locked 1000 + liquidity; reserves/prices per `updateStore`; kLast = b0·b1 with fee on, else 0; logs fee `Transfer` (if > 0), locked `Transfer` (if T = 0), `Transfer(0, to, liquidity)`, `Sync`, `Mint(caller, a0, a1)`; no other slot changes. | P1, P2, P3, P8, for the feeTo answer: `ScopedSep [balanceOf preimages of to, feeTo, 0]` |
| burn | `Pair.BurnSpec` / `BurnTarget` | Locked → `LOCKED`. A success, with L = balanceOf[pair] before the call and T = totalSupply + fee: amount0 = L·b0/T, amount1 = L·b1/T, both > 0; requests are balanceOf ×2, feeTo(), transfer(to, amount0) on token0, transfer(to, amount1) on token1 (both accepted), balanceOf ×2 again (b0', b1' < 2^112); returns the amounts; totalSupply = T − L; balanceOf[pair] = old + (fee if feeTo = pair) − L; reserves/prices per `updateStore` with b0', b1'; kLast = b0'·b1' with fee on, else 0; logs fee `Transfer`, `Transfer(pair, 0, L)`, `Sync`, `Burn(caller, amount0, amount1, to)`; no other slot changes. | P1, P2, P3, P8, for the feeTo answer: `ScopedSep [balanceOf preimages of pair, feeTo, 0]` |
| swap | `Pair.SwapSpec` / `SwapTarget` | Locked → `LOCKED`; both outs 0 → `INSUFFICIENT_OUTPUT_AMOUNT`; an out ≥ its reserve → `INSUFFICIENT_LIQUIDITY`; to = token0 or token1 → `INVALID_TO`. A success made the optimistic transfers (only for positive outs, accepted) and, for nonempty data, `uniswapV2Call(caller, out0, out1, data)` on `to` (which has code; succeeded), then asked both balances b0, b1 (< 2^112); in_i = b_i − (r_i − out_i) when positive, else 0; at least one in is positive; (1000·b0 − 3·in0)(1000·b1 − 3·in1) ≥ 1000²·r0·r1; storage is exactly `updateStore` with (b0, b1); logs `Sync(b0, b1)`, `Swap(caller, in0, in1, out0, out1, to)`; no return data. | P1, P2, P3, P8; no hash premise (writes only fixed slots); data < 2^32 bytes |

## UniswapV2Factory (Factory.lean)

Slots: `feeTo` 0, `feeToSetter` 1, `getPair` 2, `allPairs` 3 (element i at keccak256(3) + i).

| Function | Lean | Statement in plain English | Premises |
|---|---|---|---|
| createPair | `Factory.CreatePairSpec` / `CreatePairTarget` | tokenA = tokenB → `IDENTICAL_ADDRESSES`; else token0 = 0 → `ZERO_ADDRESS`; else getPair[token0][token1] ≠ 0 → `PAIR_EXISTS`. A success made the CREATE2 (salt keccak256(token0 ‖ token1), succeeded) then `initialize(token0, token1)` on pair = CREATE2 address of (factory, salt, initHash) (has code, succeeded), and nothing else; getPair in both directions = pair; allPairs.length was < 2^64 and grows by one with allPairs[n] = pair; logs `PairCreated(token0, token1, pair, n + 1)`; returns pair; no other slot changes. | P1, P2, P3, P6, P8, `ScopedSep (createPairFootprint token0 token1)`, P5 `ArrayApart` |
| setFeeTo | `Factory.SetFeeToSpec` / `SetterTarget` | Succeeds iff the caller is feeToSetter; then feeTo = the argument (upper 96 bits of the slot kept), nothing else; otherwise `UniswapV2: FORBIDDEN`. | P2, P3 |
| setFeeToSetter | `Factory.SetFeeToSetterSpec` / `SetterTarget` | The same for feeToSetter. | P2, P3 |

## Premises needing review

- **P1 No reentrant writes.** The `World` has no storage component: no answer to an external call changes the calling contract's storage. Every function that calls out (sync, skim, mint, burn, swap, createPair) is specified only for such worlds. A token or callee that calls back into the pair's unlocked ERC20 functions (transfer, approve, transferFrom, permit) during a call is outside the statements (the same premise as `PairFramed` in PairSpec/Inputs.lean).
- **P2 Caller as a parameter.** Every statement takes `msg.sender` from `Env`. Today's certified edges fix the caller to 0x2000 (`SolarTV.Call` has no caller field), so connecting these to E3–E5 instantiates the caller at 0x2000 until that bridge exists.
- **P3 Valid calls only.** `msg.value = 0`, clean ABI arguments (addresses < 2^160, words < 2^256, permit's v < 256, swap's data < 2^32 bytes), a well-formed `Env`, and storage of words indexed modulo 2^256 (`Words`). Short or dirty call data is not specified. The models revert with no data on nonzero value, but no `…Spec` states it.
- **P4 Footprint hash premises** (`ScopedSep`, never global): transfer {caller, to}; transferFrom (`transferFromFootprint`); permit {nonces[owner], allowance[owner][spender]}; mint {balanceOf of to, feeTo, 0}; burn {balanceOf of pair, feeTo, 0}; createPair {getPair[t0][t1], getPair[t1][t0]}. For mint and burn, feeTo is the factory's answer, so the premise is quantified over that answer. Each is satisfiable (`SolidCore.Spec.exists_separatedBy`). approve, initialize, getReserves, sync, skim, swap and the setters need none.
- **P5 `Factory.ArrayApart`.** allPairs[n]'s slot (keccak256(3) + n, an offset, not a hash image) is ≥ 4 and differs from both getPair slots of the call. This is avoidance, not injectivity, and it does not follow from `ScopedSep`.
- **P6 `initHash` is a parameter** of createPair: keccak256 of the pair's creation code is not computed here. The statement holds for every initHash; its value at solar's emitted creation code is the one that matters.
- **P7 `World.ecrecover`** is an abstract function (the precompile's answer, 0 on failure); secp256k1 is not modelled.
- **P8 Answers by position.** The i-th request is answered by `ans i req`, and `hasCode` is fixed for the whole call (code created or destroyed during the call is not modelled). createPair also assumes no code at address 0 (`W.hasCode 0 = false`). A failed CREATE2 gives the pair address 0, and its `initialize` call must then revert.

## Where the specifications are weaker than the source

- **W1 `Math.sqrt`** is stated as the floor square root (`Nat.sqrt`). That the source's Babylonian loop computes it, and terminates, is a proof obligation.
- **W2 SafeMath** is stated by its meaning (revert iff the exact result leaves [0, 2^256)), not by the source's wrap-then-compare check. The two are equal on words, but that is a proof obligation.
- **W3 Decoding failures** (return data under 32 bytes, an address ≥ 2^160, a bool word above 1) are taken to revert with empty data, as solc 0.8 does. This is to be checked against SolidCore's semantics.
- **W4 Targets of mint, burn, swap and skim are not full iffs.** They state what every success satisfies and the listed reverts. The other revert paths (bubbled callee reverts, decoding failures, SafeMath overflow in the fee or liquidity arithmetic, `INSUFFICIENT_LIQUIDITY_MINTED` and `_BURNED` as reverts, `OVERFLOW`, `TRANSFER_FAILED`, `INSUFFICIENT_INPUT_AMOUNT`, `K`, division by zero at zero reserves or supply) are exact only in the `…Result` models, which a reviewer must then accept as the reference. The ERC20 functions, initialize, getReserves, sync, createPair's argument checks and the setters are stated as iffs.
- **W5 Frames are slot-level** (`FrameOutside`: no slot outside the listed ones changes). "Every other key's balance or allowance is unchanged" is not stated, since it needs global separation, which is refuted (CERTIFICATION_TARGET.md, Hash premises).
- **W6 Not modelled:** gas and out-of-gas, call depth, the gas forwarded to callees, return data size limits, the `STATICCALL` to ecrecover as a request, and the callees' own effects (only their answers are modelled).
- **W7 Address writes keep the slot's upper 96 bits** and address reads mask to 160 bits (Solidity's masked update). This differs from "slot := address" only on storage the constructor never wrote.
- **W8 Not specified:** the constructors and every public getter (name, symbol, decimals, totalSupply, balanceOf, allowance, DOMAIN_SEPARATOR, PERMIT_TYPEHASH, nonces, MINIMUM_LIQUIDITY, factory, token0, token1, price0/1CumulativeLast, kLast, feeTo, feeToSetter, getPair, allPairs, allPairsLength).
- **W9 Assumed code-generation details:** `allPairs.push` panics with 0x41 at length 2^64; function arguments are evaluated left to right (sync's `_update` arguments, swap's adjusted balances), which affects only which revert data or request order appears.
- **W10 createPair's CREATE2** is an open-world request whose success the world decides. The address is the CREATE2 formula; the new pair's constructor effect (factory := msg.sender) is not stated.
- **W11 Constants.** Selectors and topics are computed from signature strings. Examples.lean checks by evaluation the 8 selectors the pair's requests and dispatch use, all 7 event topics and PERMIT_TYPEHASH against their published values. The CREATE2 init-code hash is not checked (P6).

## Behaviour of the source the statements keep (not weakenings; worth a reviewer's eye)

- initialize is callable by the factory any number of times.
- permit uses the stored DOMAIN_SEPARATOR (chain id fixed at deployment) and does not restrict s or v beyond ecrecover's answer.
- transferFrom never decreases an allowance of 2^256 − 1.
- skim and sync are callable by anyone; swap's callback receives `msg.sender` of the swap, not the pair's caller chain.

## Concrete runs (Examples.lean, by evaluation)

A first mint of balances (4000, 9000) returns 5000. A locked pair reverts with `LOCKED`. A swap of 100 token1 out of (1000, 1000) paying 100 in fails `K`, and paying 112 in syncs to (1112, 900). A swap to token0 is `INVALID_TO`. A burn with no LP held is `INSUFFICIENT_LIQUIDITY_BURNED`. setFeeTo from a non-setter is `FORBIDDEN`.
