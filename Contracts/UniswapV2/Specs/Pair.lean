import Contracts.UniswapV2.Specs.ERC20

/-!
# UniswapV2Pair: initialize, getReserves, sync, skim, mint, burn, swap

Storage layout of the port's `UniswapV2Pair`: the ERC20 slots 0 to 4 (ERC20.lean), then
`factory` 5, `token0` 6, `token1` 7, `reserve0 | reserve1 | blockTimestampLast` packed in 8 (bits
0–111, 112–223, 224–255), `price0CumulativeLast` 9, `price1CumulativeLast` 10, `kLast` 11,
`unlocked` 12 (the constants `MINIMUM_LIQUIDITY` and `SELECTOR` take no slot). The pair's ERC20
functions are ERC20.lean's at the same slots.

The pair calls its tokens (`balanceOf`, `transfer`), its factory (`feeTo()`) and, in `swap`, the
recipient (`uniswapV2Call`). The model takes each answer from the `World` by its position, and
**the world never writes the pair's storage** (Common.lean): a token or callee that re-enters the
pair's unlocked ERC20 functions and changes its storage during a call is outside these
statements. The locked functions revert on re-entry (`UniswapV2: LOCKED`), which is a property of
the world's answers here, not of the model.

For each function: `…Result` (the sequential model; exact, from any storage and any answers),
`…Target` (the key properties in the words of the storage before the call and the world's
answers) and `…Spec` (the statement to prove: the model meets the target on the valid calls,
under the named premises).
-/

namespace SolidCore.Spec.UniswapV2.Specs.Pair

open SolidCore.Spec.UniswapV2.Specs SolidCore.Spec.UniswapV2.Specs.ERC20 SolidCore.Refinement.Generic

/-! ## Layout, events, requests -/

abbrev factorySlot : Nat := 5
abbrev token0Slot : Nat := 6
abbrev token1Slot : Nat := 7
abbrev reservesSlot : Nat := 8
abbrev price0Slot : Nat := 9
abbrev price1Slot : Nat := 10
abbrev kLastSlot : Nat := 11
abbrev unlockedSlot : Nat := 12
/-- `MINIMUM_LIQUIDITY`. -/
abbrev minimumLiquidity : Nat := 1000

/-- `reserve0` of the packed word. -/
def reserve0Of (w : Nat) : Nat := w % U112
/-- `reserve1` of the packed word. -/
def reserve1Of (w : Nat) : Nat := w / U112 % U112
/-- `blockTimestampLast` of the packed word. -/
def tsLastOf (w : Nat) : Nat := w / 2 ^ 224 % U32
/-- The packed word of `(reserve0, reserve1, blockTimestampLast)`. -/
def packReserves (r0 r1 ts : Nat) : Nat := r0 + r1 * U112 + ts * 2 ^ 224

/-- `Sync(uint112,uint112)`. -/
def syncTopic : Nat := topicOf "Sync(uint112,uint112)"
/-- `Mint(address,uint256,uint256)`. -/
def mintTopic : Nat := topicOf "Mint(address,uint256,uint256)"
/-- `Burn(address,uint256,uint256,address)`. -/
def burnTopic : Nat := topicOf "Burn(address,uint256,uint256,address)"
/-- `Swap(address,uint256,uint256,uint256,uint256,address)`. -/
def swapTopic : Nat := topicOf "Swap(address,uint256,uint256,uint256,uint256,address)"

def syncLog (b0 b1 : Nat) : List Nat × List Nat := ([syncTopic], be32 b0 ++ be32 b1)
def mintLog (s a0 a1 : Nat) : List Nat × List Nat := ([mintTopic, s], be32 a0 ++ be32 a1)
def burnLog (s a0 a1 dst : Nat) : List Nat × List Nat := ([burnTopic, s, dst], be32 a0 ++ be32 a1)
def swapLog (s i0 i1 o0 o1 dst : Nat) : List Nat × List Nat :=
  ([swapTopic, s, dst], be32 i0 ++ be32 i1 ++ be32 o0 ++ be32 o1)

/-- `balanceOf(address(this))` of the token `tok`. -/
def balQ (env : Env) (tok : Nat) : Req := .call tok (calldata "balanceOf(address)" [env.self])
/-- `feeTo()` of the factory `f`. -/
def feeQ (f : Nat) : Req := .call f (calldata "feeTo()" [])
/-- `transfer(dst, v)` of the token `tok`. -/
def transferQ (tok dst v : Nat) : Req := .call tok (transferData dst v)
/-- `uniswapV2Call(sender, a0, a1, data)`'s call data: the head, the offset `0x80`, the length and
the data padded to whole words. -/
def uniswapV2CallData (sender a0 a1 : Nat) (data : List Nat) : List Nat :=
  be 4 (selectorOf "uniswapV2Call(address,uint256,uint256,bytes)") ++ be32 sender ++ be32 a0 ++
    be32 a1 ++ be32 0x80 ++ be32 data.length ++ padWords data

/-! ## The pre-state, by name -/

def r0Of (st : Store) : Nat := reserve0Of (st reservesSlot)
def r1Of (st : Store) : Nat := reserve1Of (st reservesSlot)
def tok0 (st : Store) : Nat := st token0Slot % U160
def tok1 (st : Store) : Nat := st token1Slot % U160
def factoryOf (st : Store) : Nat := st factorySlot % U160

/-- A revert with the data `d`: no change, no log, no request. -/
def Reverts (st : Store) (d : List Nat) (r : Result) : Prop :=
  r.success = false ∧ r.output = d ∧ r.storage = st ∧ r.logs = [] ∧ r.calls = []

/-! ## Shared steps -/

/-- The `lock` modifier: `unlocked == 1` or `UniswapV2: LOCKED`; 0 during the body; 1 after. -/
def lock {α : Type} (m : M α) : M α := do
  let u ← sload unlockedSlot
  require (u = 1) (err "UniswapV2: LOCKED")
  sstore unlockedSlot 0
  let x ← m
  sstore unlockedSlot 1
  pure x

/-- An address read from its own slot (the low 160 bits). -/
def addrAt (k : Nat) : M Nat := do return (← sload k) % U160

/-- The pair's balance of `tok`, by a high-level `balanceOf` call. -/
def tokenBalance (W : World) (env : Env) (tok : Nat) : M Nat := callWord W tok (calldata "balanceOf(address)" [env.self])

/-- The cumulative price increment of `_update`: `(rNum · 2^112 / rDen) · elapsed` (UQ112x112). -/
def priceInc (rNum rDen elapsed : Nat) : Nat := rNum * U112 / rDen * elapsed

/-- `_update(b0, b1, r0, r1)`: `b0, b1 ≤ type(uint112).max` or `UniswapV2: OVERFLOW`; with
`ts = block.timestamp mod 2^32` and `elapsed = ts - blockTimestampLast mod 2^32`, when `elapsed`
and both old reserves are nonzero the cumulative prices grow (mod `2^256`) by
`priceInc r1 r0 elapsed` and `priceInc r0 r1 elapsed`; the reserves become `(b0, b1, ts)`;
`Sync(b0, b1)`. -/
def update (env : Env) (b0 b1 r0 r1 : Nat) : M Unit := do
  require (b0 < U112 ∧ b1 < U112) (err "UniswapV2: OVERFLOW")
  let ts := env.timestamp % U32
  let w ← sload reservesSlot
  let elapsed := (ts + U32 - tsLastOf w) % U32
  if 0 < elapsed ∧ r0 ≠ 0 ∧ r1 ≠ 0 then
    let p0 ← sload price0Slot
    sstore price0Slot ((p0 + priceInc r1 r0 elapsed) % U256)
    let p1 ← sload price1Slot
    sstore price1Slot ((p1 + priceInc r0 r1 elapsed) % U256)
  sstore reservesSlot (packReserves b0 b1 ts)
  emit [syncTopic] (be32 b0 ++ be32 b1)

/-- The storage after `_update(b0, b1, r0, r1)` from `st`, when it succeeds. -/
def updateStore (env : Env) (st : Store) (b0 b1 r0 r1 : Nat) : Store :=
  let ts := env.timestamp % U32
  let elapsed := (ts + U32 - tsLastOf (st reservesSlot)) % U32
  let st1 := if 0 < elapsed ∧ r0 ≠ 0 ∧ r1 ≠ 0 then
      upd (upd st price0Slot ((st price0Slot + priceInc r1 r0 elapsed) % U256)) price1Slot
        ((st price1Slot + priceInc r0 r1 elapsed) % U256)
    else st
  upd st1 reservesSlot (packReserves b0 b1 ts)

/-- The protocol fee's liquidity (`_mintFee`): with `kLast ≠ 0` and `√(r0 r1) > √kLast`,
`totalSupply · (√(r0 r1) − √kLast) / (5 √(r0 r1) + √kLast)` (one sixth of the growth of `√k`),
else 0. `√` is the floor square root (`Math.sqrt`). -/
def feeLiquidity (t kL r0 r1 : Nat) : Nat :=
  if kL = 0 then 0 else
    let rootK := Nat.sqrt (r0 * r1)
    let rootKLast := Nat.sqrt kL
    if rootKLast < rootK then t * (rootK - rootKLast) / (rootK * 5 + rootKLast) else 0

/-- `_mintFee(r0, r1)`: asks the factory for `feeTo`; fee on iff `feeTo ≠ 0`; fee on and the
fee liquidity positive mints it to `feeTo`; fee off clears a nonzero `kLast`. Returns fee on.
`Math.sqrt` is stated as the floor square root. -/
def mintFee (W : World) (r0 r1 : Nat) : M Bool := do
  let f ← addrAt factorySlot
  let feeTo ← callAddress W f (calldata "feeTo()" [])
  let kL ← sload kLastSlot
  if feeTo ≠ 0 then
    if kL ≠ 0 then
      let p ← mul r0 r1
      let rootK := Nat.sqrt p
      let rootKLast := Nat.sqrt kL
      if rootKLast < rootK then
        let t ← sload totalSupplySlot
        let g ← sub rootK rootKLast
        let num ← mul t g
        let k5 ← mul rootK 5
        let den ← add k5 rootKLast
        let liq ← div num den
        if 0 < liq then mintLP feeTo liq
    return true
  else
    if kL ≠ 0 then sstore kLastSlot 0
    return false

/-- After a liquidity event with the fee on: `kLast = reserve0 · reserve1` (SafeMath). -/
def setKLast (feeOn : Bool) : M Unit := do
  if feeOn then
    let w ← sload reservesSlot
    let k ← mul (reserve0Of w) (reserve1Of w)
    sstore kLastSlot k

/-! ## initialize(address token0, address token1) -/

/-- The sequential model: only the factory; sets `token0` and `token1`. -/
def initializeResult (env : Env) (st : Store) (t0 t1 : Nat) : Result := run st do
  nonpayable env
  let f ← addrAt factorySlot
  require (env.caller = f) (err "UniswapV2: FORBIDDEN")
  sstoreAddr token0Slot t0
  sstoreAddr token1Slot t1
  return []

/-- **initialize's target**: success iff the caller is `factory`; then `token0`, `token1` hold the
arguments (upper 96 bits of their slots kept) and nothing else changes; no log, no return data;
otherwise `UniswapV2: FORBIDDEN`. Not locked, not once-only: the factory may call it again. -/
def InitializeTarget (env : Env) (st : Store) (t0 t1 : Nat) (r : Result) : Prop :=
  (r.success = true ↔ env.caller = factoryOf st) ∧
  (r.success = true → r.storage = upd (upd st token0Slot (setLow160 (st token0Slot) t0)) token1Slot
      (setLow160 (st token1Slot) t1) ∧ r.logs = [] ∧ r.output = [] ∧ r.calls = []) ∧
  (r.success = false → Reverts st (err "UniswapV2: FORBIDDEN") r)

/-- **initialize's statement.** No hash premise. -/
def InitializeSpec : Prop :=
  ∀ env st t0 t1, ValidCall env st → Clean [t0, t1] [] →
    InitializeTarget env st t0 t1 (initializeResult env st t0 t1)

/-! ## getReserves() returns (uint112, uint112, uint32) -/

def getReservesResult (env : Env) (st : Store) : Result := run st do
  nonpayable env
  let w ← sload reservesSlot
  return be32 (reserve0Of w) ++ be32 (reserve1Of w) ++ be32 (tsLastOf w)

/-- **getReserves' target**: succeeds, returns the three packed fields, changes nothing. -/
def GetReservesTarget (st : Store) (r : Result) : Prop :=
  r.success = true ∧ r.storage = st ∧ r.logs = [] ∧ r.calls = [] ∧
    r.output = be32 (r0Of st) ++ be32 (r1Of st) ++ be32 (tsLastOf (st reservesSlot))

def GetReservesSpec : Prop :=
  ∀ env st, ValidCall env st → GetReservesTarget st (getReservesResult env st)

/-! ## sync() -/

def syncResult (env : Env) (W : World) (st : Store) : Result := run st do
  nonpayable env
  lock do
    let t0 ← addrAt token0Slot
    let b0 ← tokenBalance W env t0
    let t1 ← addrAt token1Slot
    let b1 ← tokenBalance W env t1
    let w ← sload reservesSlot
    update env b0 b1 (reserve0Of w) (reserve1Of w)
    return []

/-- **sync's target**: `unlocked ≠ 1` reverts with `LOCKED`; otherwise it asks `token0` then
`token1` for the pair's balances and succeeds iff both answer a word and both fit `uint112`; then
the reserves are the balances, the timestamp is `block.timestamp mod 2^32`, the cumulative prices
grow as `update` says, `Sync(b0, b1)` is logged, and nothing else changes. -/
def SyncTarget (env : Env) (W : World) (st : Store) (r : Result) : Prop :=
  let q0 := balQ env (tok0 st)
  let q1 := balQ env (tok1 st)
  (st unlockedSlot ≠ 1 → Reverts st (err "UniswapV2: LOCKED") r) ∧
  (r.success = true ↔ st unlockedSlot = 1 ∧
    ∃ b0 b1, ReturnsWord (W.ans 0 q0) b0 ∧ ReturnsWord (W.ans 1 q1) b1 ∧ b0 < U112 ∧ b1 < U112) ∧
  (∀ b0 b1, r.success = true → ReturnsWord (W.ans 0 q0) b0 → ReturnsWord (W.ans 1 q1) b1 →
    r.calls = [q0, q1] ∧ r.storage = updateStore env st b0 b1 (r0Of st) (r1Of st) ∧
    r.logs = [syncLog b0 b1] ∧ r.output = []) ∧
  (r.success = false → r.storage = st ∧ r.logs = [] ∧ r.calls = [])

/-- **sync's statement.** No hash premise; the world writes no pair storage (model). -/
def SyncSpec : Prop := ∀ env W st, ValidCall env st → SyncTarget env W st (syncResult env W st)

/-! ## skim(address to) -/

def skimResult (env : Env) (W : World) (st : Store) (dst : Nat) : Result := run st do
  nonpayable env
  lock do
    let t0 ← addrAt token0Slot
    let t1 ← addrAt token1Slot
    let b0 ← tokenBalance W env t0
    let w0 ← sload reservesSlot
    let x0 ← sub b0 (reserve0Of w0)
    safeTransfer W t0 dst x0
    let b1 ← tokenBalance W env t1
    let w1 ← sload reservesSlot
    let x1 ← sub b1 (reserve1Of w1)
    safeTransfer W t1 dst x1
    return []

/-- **skim's target**: `LOCKED` as sync; a success has asked `token0`'s balance `b0 ≥ reserve0`,
sent `b0 − reserve0` of `token0` to `to`, then the same for `token1` (four requests in that order,
both transfers accepted), and changes no storage, logs nothing and returns nothing; a balance below
its reserve reverts with `ds-math-sub-underflow`. -/
def SkimTarget (env : Env) (W : World) (st : Store) (dst : Nat) (r : Result) : Prop :=
  let q0 := balQ env (tok0 st)
  let q1 := balQ env (tok1 st)
  (st unlockedSlot ≠ 1 → Reverts st (err "UniswapV2: LOCKED") r) ∧
  (r.success = true → ∃ b0 b1, ReturnsWord (W.ans 0 q0) b0 ∧ ReturnsWord (W.ans 2 q1) b1 ∧
    r0Of st ≤ b0 ∧ r1Of st ≤ b1 ∧
    r.calls = [q0, transferQ (tok0 st) dst (b0 - r0Of st), q1, transferQ (tok1 st) dst (b1 - r1Of st)] ∧
    TransferAccepted (W.ans 1 (transferQ (tok0 st) dst (b0 - r0Of st))) ∧
    TransferAccepted (W.ans 3 (transferQ (tok1 st) dst (b1 - r1Of st))) ∧
    r.storage = st ∧ r.logs = [] ∧ r.output = []) ∧
  (∀ b0, st unlockedSlot = 1 → ReturnsWord (W.ans 0 q0) b0 → b0 < r0Of st →
    Reverts st (err "ds-math-sub-underflow") r) ∧
  (r.success = false → r.storage = st ∧ r.logs = [] ∧ r.calls = [])

/-- **skim's statement.** No hash premise; the world writes no pair storage (model). -/
def SkimSpec : Prop :=
  ∀ env W st dst, ValidCall env st → Clean [dst] [] → SkimTarget env W st dst (skimResult env W st dst)

/-! ## mint(address to) returns (uint liquidity) -/

def mintResult (env : Env) (W : World) (st : Store) (dst : Nat) : Result := run st do
  nonpayable env
  lock do
    let w ← sload reservesSlot
    let r0 := reserve0Of w
    let r1 := reserve1Of w
    let t0 ← addrAt token0Slot
    let b0 ← tokenBalance W env t0
    let t1 ← addrAt token1Slot
    let b1 ← tokenBalance W env t1
    let a0 ← sub b0 r0
    let a1 ← sub b1 r1
    let feeOn ← mintFee W r0 r1
    let ts ← sload totalSupplySlot
    let liq ← if ts = 0 then do
        let p ← mul a0 a1
        let l ← sub (Nat.sqrt p) minimumLiquidity
        mintLP 0 minimumLiquidity
        pure l
      else do
        let x ← mul a0 ts
        let x ← div x r0
        let y ← mul a1 ts
        let y ← div y r1
        pure (min x y)
    require (0 < liq) (err "UniswapV2: INSUFFICIENT_LIQUIDITY_MINTED")
    mintLP dst liq
    update env b0 b1 r0 r1
    setKLast feeOn
    emit [mintTopic, env.caller] (be32 a0 ++ be32 a1)
    return be32 liq

/-- The fee the call mints to `feeTo` (0 when the fee is off). -/
def feeOf (st : Store) (feeTo : Nat) : Nat :=
  if feeTo ≠ 0 then feeLiquidity (st totalSupplySlot) (st kLastSlot) (r0Of st) (r1Of st) else 0

/-- The footprint of mint and burn: the balance slots of `to` (or the pair), `feeTo` and
address 0. `feeTo` is the factory's answer, so the premise is stated per answer. -/
def liquidityFootprint (dst feeTo : Nat) : List (List Nat) :=
  [pre dst balanceOfSlot, pre feeTo balanceOfSlot, pre 0 balanceOfSlot]

/-- **mint's target**, with `r0, r1` the reserves before the call, `b0, b1` the tokens' answers,
`a0 = b0 − r0`, `a1 = b1 − r1`, `feeTo` the factory's answer, `fee = feeOf st feeTo` and
`T = totalSupply + fee`:
* `LOCKED` as sync; a balance below its reserve reverts with `ds-math-sub-underflow`;
* a success asked `balanceOf` of `token0`, `token1`, then `feeTo()`, and nothing else; minted
  `liquidity = √(a0 a1) − 1000` when `T = 0` (and 1000 locked at address 0), else
  `min(a0 T / r0, a1 T / r1)`, positive; returns it; `balanceOf[to]` grew by it (and by the fee
  when `to = feeTo`, and by 1000 when `to = 0` and `T = 0`); `totalSupply` grew by the fee, the
  locked 1000 and the liquidity; reserves and prices as `update` says with `b0, b1 < 2^112`;
  `kLast = b0 b1` with the fee on, else 0; logs the fee's `Transfer` (when positive), the locked
  `Transfer` (when `T = 0`), `Transfer(0, to, liquidity)`, `Sync(b0, b1)`,
  `Mint(caller, a0, a1)`; no other slot changes. -/
def MintTarget (env : Env) (W : World) (st : Store) (dst : Nat) (r : Result) : Prop :=
  let r0 := r0Of st
  let r1 := r1Of st
  let q0 := balQ env (tok0 st)
  let q1 := balQ env (tok1 st)
  let qf := feeQ (factoryOf st)
  (st unlockedSlot ≠ 1 → Reverts st (err "UniswapV2: LOCKED") r) ∧
  (∀ b0 b1, st unlockedSlot = 1 → ReturnsWord (W.ans 0 q0) b0 → ReturnsWord (W.ans 1 q1) b1 →
    (b0 < r0 ∨ b1 < r1) → Reverts st (err "ds-math-sub-underflow") r) ∧
  (r.success = true → ∃ b0 b1 feeTo liq,
    ReturnsWord (W.ans 0 q0) b0 ∧ ReturnsWord (W.ans 1 q1) b1 ∧ ReturnsWord (W.ans 2 qf) feeTo ∧
    feeTo < U160 ∧ r0 ≤ b0 ∧ r1 ≤ b1 ∧ b0 < U112 ∧ b1 < U112 ∧
    let a0 := b0 - r0
    let a1 := b1 - r1
    let fee := feeOf st feeTo
    let T := st totalSupplySlot + fee
    r.calls = [q0, q1, qf] ∧ r.output = be32 liq ∧ 0 < liq ∧
    (T = 0 → liq = Nat.sqrt (a0 * a1) - minimumLiquidity) ∧
    (T ≠ 0 → liq = min (a0 * T / r0) (a1 * T / r1)) ∧
    r.storage totalSupplySlot = T + (if T = 0 then minimumLiquidity else 0) + liq ∧
    r.storage (balKey dst) = st (balKey dst) + (if dst = feeTo then fee else 0) +
      (if dst = 0 ∧ T = 0 then minimumLiquidity else 0) + liq ∧
    (feeTo ≠ dst → feeTo ≠ 0 → r.storage (balKey feeTo) = st (balKey feeTo) + fee) ∧
    (dst ≠ 0 → r.storage (balKey 0) = st (balKey 0) + (if T = 0 then minimumLiquidity else 0)) ∧
    (∀ k ∈ [reservesSlot, price0Slot, price1Slot], r.storage k = updateStore env st b0 b1 r0 r1 k) ∧
    r.storage kLastSlot = (if feeTo ≠ 0 then b0 * b1 else 0) ∧
    r.storage unlockedSlot = 1 ∧
    FrameOutside st r.storage [totalSupplySlot, reservesSlot, price0Slot, price1Slot, kLastSlot,
      unlockedSlot, balKey dst, balKey feeTo, balKey 0] ∧
    r.logs = (if 0 < fee then [transferLog 0 feeTo fee] else []) ++
      (if T = 0 then [transferLog 0 0 minimumLiquidity] else []) ++
      [transferLog 0 dst liq, syncLog b0 b1, mintLog env.caller a0 a1]) ∧
  (r.success = false → r.storage = st ∧ r.logs = [] ∧ r.calls = [])

/-- **mint's statement.** Premise: for the factory's answer `feeTo`, `ScopedSep
(liquidityFootprint to feeTo)`; the world writes no pair storage (model). -/
def MintSpec : Prop :=
  ∀ env W st dst, ValidCall env st → Clean [dst] [] →
    (∀ feeTo, ReturnsWord (W.ans 2 (feeQ (factoryOf st))) feeTo → ScopedSep (liquidityFootprint dst feeTo)) →
    MintTarget env W st dst (mintResult env W st dst)

/-! ## burn(address to) returns (uint amount0, uint amount1) -/

def burnResult (env : Env) (W : World) (st : Store) (dst : Nat) : Result := run st do
  nonpayable env
  lock do
    let w ← sload reservesSlot
    let r0 := reserve0Of w
    let r1 := reserve1Of w
    let t0 ← addrAt token0Slot
    let t1 ← addrAt token1Slot
    let b0 ← tokenBalance W env t0
    let b1 ← tokenBalance W env t1
    let liq ← sload (balKey env.self)
    let feeOn ← mintFee W r0 r1
    let ts ← sload totalSupplySlot
    let x ← mul liq b0
    let a0 ← div x ts
    let y ← mul liq b1
    let a1 ← div y ts
    require (0 < a0 ∧ 0 < a1) (err "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED")
    burnLP env.self liq
    safeTransfer W t0 dst a0
    safeTransfer W t1 dst a1
    let b0' ← tokenBalance W env t0
    let b1' ← tokenBalance W env t1
    update env b0' b1' r0 r1
    setKLast feeOn
    emit [burnTopic, env.caller, dst] (be32 a0 ++ be32 a1)
    return be32 a0 ++ be32 a1

/-- **burn's target**, with `L = balanceOf[pair]` before the call, `b0, b1` the tokens' first
answers, `feeTo` the factory's, `fee = feeOf st feeTo`, `T = totalSupply + fee`:
* `LOCKED` as sync;
* a success has `amount0 = L b0 / T`, `amount1 = L b1 / T`, both positive; asked
  `balanceOf` of both tokens, `feeTo()`, sent `amount0` of `token0` and `amount1` of `token1` to
  `to` (both accepted), asked both balances again (`b0', b1' < 2^112`); returns the two amounts;
  burnt `L` from the pair (`totalSupply = T − L`; `balanceOf[pair]` is the fee when `feeTo` is
  the pair, else 0 more than before minus `L`); reserves and prices as `update` says with
  `b0', b1'`; `kLast = b0' b1'` with the fee on, else 0; logs the fee's `Transfer` (when
  positive), `Transfer(pair, 0, L)`, `Sync(b0', b1')`, `Burn(caller, amount0, amount1, to)`; no
  other slot changes. -/
def BurnTarget (env : Env) (W : World) (st : Store) (dst : Nat) (r : Result) : Prop :=
  let r0 := r0Of st
  let r1 := r1Of st
  let q0 := balQ env (tok0 st)
  let q1 := balQ env (tok1 st)
  let qf := feeQ (factoryOf st)
  let L := st (balKey env.self)
  (st unlockedSlot ≠ 1 → Reverts st (err "UniswapV2: LOCKED") r) ∧
  (r.success = true → ∃ b0 b1 feeTo b0' b1',
    ReturnsWord (W.ans 0 q0) b0 ∧ ReturnsWord (W.ans 1 q1) b1 ∧ ReturnsWord (W.ans 2 qf) feeTo ∧
    feeTo < U160 ∧
    let fee := feeOf st feeTo
    let T := st totalSupplySlot + fee
    let a0 := L * b0 / T
    let a1 := L * b1 / T
    0 < T ∧ 0 < a0 ∧ 0 < a1 ∧
    r.calls = [q0, q1, qf, transferQ (tok0 st) dst a0, transferQ (tok1 st) dst a1, q0, q1] ∧
    TransferAccepted (W.ans 3 (transferQ (tok0 st) dst a0)) ∧
    TransferAccepted (W.ans 4 (transferQ (tok1 st) dst a1)) ∧
    ReturnsWord (W.ans 5 q0) b0' ∧ ReturnsWord (W.ans 6 q1) b1' ∧ b0' < U112 ∧ b1' < U112 ∧
    r.output = be32 a0 ++ be32 a1 ∧
    r.storage totalSupplySlot = T - L ∧
    r.storage (balKey env.self) = st (balKey env.self) + (if feeTo = env.self then fee else 0) - L ∧
    (feeTo ≠ env.self → feeTo ≠ 0 → r.storage (balKey feeTo) = st (balKey feeTo) + fee) ∧
    (∀ k ∈ [reservesSlot, price0Slot, price1Slot], r.storage k = updateStore env st b0' b1' r0 r1 k) ∧
    r.storage kLastSlot = (if feeTo ≠ 0 then b0' * b1' else 0) ∧
    r.storage unlockedSlot = 1 ∧
    FrameOutside st r.storage [totalSupplySlot, reservesSlot, price0Slot, price1Slot, kLastSlot,
      unlockedSlot, balKey env.self, balKey feeTo] ∧
    r.logs = (if 0 < fee then [transferLog 0 feeTo fee] else []) ++
      [transferLog env.self 0 L, syncLog b0' b1', burnLog env.caller a0 a1 dst]) ∧
  (r.success = false → r.storage = st ∧ r.logs = [] ∧ r.calls = [])

/-- **burn's statement.** Premise: for the factory's answer `feeTo`, `ScopedSep
(liquidityFootprint pair feeTo)`; the world writes no pair storage (model). -/
def BurnSpec : Prop :=
  ∀ env W st dst, ValidCall env st → Clean [dst] [] →
    (∀ feeTo, ReturnsWord (W.ans 2 (feeQ (factoryOf st))) feeTo →
      ScopedSep (liquidityFootprint env.self feeTo)) →
    BurnTarget env W st dst (burnResult env W st dst)

/-! ## swap(uint amount0Out, uint amount1Out, address to, bytes data) -/

def swapResult (env : Env) (W : World) (st : Store) (o0 o1 dst : Nat) (data : List Nat) : Result :=
  run st do
    nonpayable env
    lock do
      require (0 < o0 ∨ 0 < o1) (err "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT")
      let w ← sload reservesSlot
      let r0 := reserve0Of w
      let r1 := reserve1Of w
      require (o0 < r0 ∧ o1 < r1) (err "UniswapV2: INSUFFICIENT_LIQUIDITY")
      let t0 ← addrAt token0Slot
      let t1 ← addrAt token1Slot
      require (dst ≠ t0 ∧ dst ≠ t1) (err "UniswapV2: INVALID_TO")
      if 0 < o0 then safeTransfer W t0 dst o0
      if 0 < o1 then safeTransfer W t1 dst o1
      if 0 < data.length then callUnit W dst (uniswapV2CallData env.caller o0 o1 data)
      let b0 ← tokenBalance W env t0
      let b1 ← tokenBalance W env t1
      let i0 := if r0 - o0 < b0 then b0 - (r0 - o0) else 0
      let i1 := if r1 - o1 < b1 then b1 - (r1 - o1) else 0
      require (0 < i0 ∨ 0 < i1) (err "UniswapV2: INSUFFICIENT_INPUT_AMOUNT")
      let x0 ← mul b0 1000
      let y0 ← mul i0 3
      let adj0 ← sub x0 y0
      let x1 ← mul b1 1000
      let y1 ← mul i1 3
      let adj1 ← sub x1 y1
      let lhs ← mul adj0 adj1
      let rr ← mul r0 r1
      let rhs ← mul rr 1000000
      require (rhs ≤ lhs) (err "UniswapV2: K")
      update env b0 b1 r0 r1
      emit [swapTopic, env.caller, dst] (be32 i0 ++ be32 i1 ++ be32 o0 ++ be32 o1)
      return []

/-- The requests of a successful swap before the two balance queries: the optimistic transfers
(each only when its amount is positive), then the callback when `data` is nonempty. -/
def swapPushes (env : Env) (st : Store) (o0 o1 dst : Nat) (data : List Nat) : List Req :=
  (if 0 < o0 then [transferQ (tok0 st) dst o0] else []) ++
  (if 0 < o1 then [transferQ (tok1 st) dst o1] else []) ++
  (if 0 < data.length then [Req.call dst (uniswapV2CallData env.caller o0 o1 data)] else [])

/-- The amount in of a token: the balance above `reserve − amountOut`, else 0. -/
def amountIn (b r o : Nat) : Nat := if r - o < b then b - (r - o) else 0

/-- **swap's target**, with `r0, r1` the reserves before the call:
* `LOCKED` as sync; with the lock free: both amounts out zero reverts with
  `INSUFFICIENT_OUTPUT_AMOUNT`; else an amount out not below its reserve reverts with
  `INSUFFICIENT_LIQUIDITY`; else `to` being `token0` or `token1` reverts with `INVALID_TO`;
* a success made the optimistic transfers and the callback (`swapPushes`, each transfer accepted,
  the callback to an address with code and successful), then asked both balances `b0, b1` (both
  below `2^112`); with `in0 = amountIn b0 r0 amount0Out`, `in1 = amountIn b1 r1 amount1Out`, at
  least one is positive and the fee-adjusted product does not decrease:
  `(1000 b0 − 3 in0)(1000 b1 − 3 in1) ≥ 1000² r0 r1`; the storage is exactly `update`'s with
  `(b0, b1)` (no hash premise: swap writes only fixed slots); logs `Sync(b0, b1)` and
  `Swap(caller, in0, in1, amount0Out, amount1Out, to)`; returns nothing. -/
def SwapTarget (env : Env) (W : World) (st : Store) (o0 o1 dst : Nat) (data : List Nat)
    (r : Result) : Prop :=
  let r0 := r0Of st
  let r1 := r1Of st
  let pushes := swapPushes env st o0 o1 dst data
  let n := pushes.length
  (st unlockedSlot ≠ 1 → Reverts st (err "UniswapV2: LOCKED") r) ∧
  (st unlockedSlot = 1 → o0 = 0 → o1 = 0 → Reverts st (err "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT") r) ∧
  (st unlockedSlot = 1 → (0 < o0 ∨ 0 < o1) → ¬ (o0 < r0 ∧ o1 < r1) →
    Reverts st (err "UniswapV2: INSUFFICIENT_LIQUIDITY") r) ∧
  (st unlockedSlot = 1 → (0 < o0 ∨ 0 < o1) → o0 < r0 → o1 < r1 → (dst = tok0 st ∨ dst = tok1 st) →
    Reverts st (err "UniswapV2: INVALID_TO") r) ∧
  (r.success = true → ∃ b0 b1,
    (0 < o0 → TransferAccepted (W.ans 0 (transferQ (tok0 st) dst o0))) ∧
    (0 < o1 → TransferAccepted (W.ans (if 0 < o0 then 1 else 0) (transferQ (tok1 st) dst o1))) ∧
    (0 < data.length → W.hasCode dst = true ∧
      (W.ans (n - 1) (Req.call dst (uniswapV2CallData env.caller o0 o1 data))).ok = true) ∧
    ReturnsWord (W.ans n (balQ env (tok0 st))) b0 ∧ ReturnsWord (W.ans (n + 1) (balQ env (tok1 st))) b1 ∧
    let i0 := amountIn b0 r0 o0
    let i1 := amountIn b1 r1 o1
    r.calls = pushes ++ [balQ env (tok0 st), balQ env (tok1 st)] ∧
    (0 < i0 ∨ 0 < i1) ∧ b0 < U112 ∧ b1 < U112 ∧
    (b0 * 1000 - i0 * 3) * (b1 * 1000 - i1 * 3) ≥ r0 * r1 * 1000 ^ 2 ∧
    r.storage = updateStore env st b0 b1 r0 r1 ∧
    r.logs = [syncLog b0 b1, swapLog env.caller i0 i1 o0 o1 dst] ∧ r.output = []) ∧
  (r.success = false → r.storage = st ∧ r.logs = [] ∧ r.calls = [])

/-- **swap's statement.** No hash premise; the world writes no pair storage (model). -/
def SwapSpec : Prop :=
  ∀ env W st o0 o1 dst data, ValidCall env st → Clean [dst] [o0, o1] → data.length < U32 →
    (∀ b ∈ data, b < 256) → SwapTarget env W st o0 o1 dst data (swapResult env W st o0 o1 dst data)

end SolidCore.Spec.UniswapV2.Specs.Pair
