import Contracts.UniswapV2.Specs.Common

/-!
# UniswapV2Factory: createPair, setFeeTo, setFeeToSetter

Storage layout of the port's `UniswapV2Factory`: `feeTo` 0, `feeToSetter` 1, `getPair` 2 (a
nested mapping), `allPairs` 3 (its length; element `i` at `keccak256(3) + i`).

`createPair` deploys the pair with `CREATE2` of `type(UniswapV2Pair).creationCode` and the salt
`keccak256(abi.encodePacked(token0, token1))`, then calls its `initialize`. The model takes the
`CREATE2` as the call's first external request (succeeds or fails, as the source semantics treats
it: an open-world request), and the init code's hash `initHash` as a parameter: the statement is
about every `initHash`, and its instance at the real one (keccak256 of the pair's creation code
solar emits) is the one that matters. The deployed address is stated by the `CREATE2` formula.
-/

namespace SolidCore.Spec.UniswapV2.Specs.Factory

open SolidCore.Spec.UniswapV2.Specs SolidCore.Refinement.Generic

abbrev feeToSlot : Nat := 0
abbrev feeToSetterSlot : Nat := 1
abbrev getPairSlot : Nat := 2
abbrev allPairsSlot : Nat := 3

/-- The slot of `getPair[a][b]`. -/
def pairKey (a b : Nat) : Nat := solHash b (solHash a getPairSlot)
/-- The slot of `allPairs[0]`: `keccak256(3)`. -/
def allPairsBase : Nat := keccak (be32 allPairsSlot)
/-- The slot of `allPairs[i]`. -/
def allPairsKey (i : Nat) : Nat := (allPairsBase + i) % U256

/-- `(token0, token1)`: the two addresses in increasing order. -/
def sortTokens (a b : Nat) : Nat × Nat := if a < b then (a, b) else (b, a)
/-- The pair's salt: `keccak256(abi.encodePacked(token0, token1))` (20 bytes each). -/
def pairSalt (t0 t1 : Nat) : Nat := keccak (be 20 t0 ++ be 20 t1)
/-- The `CREATE2` address: the low 160 bits of `keccak256(0xff ‖ deployer ‖ salt ‖ initHash)`. -/
def create2Address (deployer salt initHash : Nat) : Nat :=
  keccak ([0xff] ++ be 20 deployer ++ be32 salt ++ be32 initHash) % U160

/-- `PairCreated(address,address,address,uint256)`. -/
def pairCreatedTopic : Nat := topicOf "PairCreated(address,address,address,uint256)"

/-- `initialize(token0, token1)` of the pair `p`. -/
def initQ (p t0 t1 : Nat) : Req := .call p (calldata "initialize(address,address)" [t0, t1])

/-- A revert with the data `d`: no change, no log, no request. -/
def Reverts (st : Store) (d : List Nat) (r : Result) : Prop :=
  r.success = false ∧ r.output = d ∧ r.storage = st ∧ r.logs = [] ∧ r.calls = []

/-- Every slot outside `ks` is as in `st`. -/
def FrameOutside (st st' : Store) (ks : List Nat) : Prop := ∀ n, (n % U256) ∉ ks → st' n = st n

/-! ## createPair(address tokenA, address tokenB) returns (address pair) -/

def createPairResult (env : Env) (W : World) (initHash : Nat) (st : Store) (a b : Nat) : Result :=
  run st do
    nonpayable env
    require (a ≠ b) (err "UniswapV2: IDENTICAL_ADDRESSES")
    let t0 := (sortTokens a b).1
    let t1 := (sortTokens a b).2
    require (t0 ≠ 0) (err "UniswapV2: ZERO_ADDRESS")
    let p ← sload (pairKey t0 t1)
    require (p % U160 = 0) (err "UniswapV2: PAIR_EXISTS")
    let salt := pairSalt t0 t1
    let c ← request W (.create2 salt)
    let pair := if c.ok then create2Address env.self salt initHash else 0
    callUnit W pair (calldata "initialize(address,address)" [t0, t1])
    sstoreAddr (pairKey t0 t1) pair
    sstoreAddr (pairKey t1 t0) pair
    let n ← sload allPairsSlot
    require (n < 2 ^ 64) (panicData 0x41)
    sstore allPairsSlot (n + 1)
    sstoreAddr (allPairsKey n) pair
    emit [pairCreatedTopic, t0, t1] (be32 pair ++ be32 (n + 1))
    return be32 pair

/-- The footprint of createPair: `getPair[token0][token1]` and `getPair[token1][token0]` (inner and
outer preimages). -/
def createPairFootprint (t0 t1 : Nat) : List (List Nat) :=
  SolidCore.Spec.HashScopeNested.nestedFootprint getPairSlot t0 t1 ++
    SolidCore.Spec.HashScopeNested.nestedFootprint getPairSlot t1 t0

/-- **The array premise**: `allPairs[n]`'s slot (`keccak256(3) + n`, an offset, not a hash image)
is none of the fixed slots and neither `getPair` slot of the call. Avoidance of four small
values and two words, not injectivity; not implied by `ScopedSep`. -/
def ArrayApart (t0 t1 n : Nat) : Prop :=
  4 ≤ allPairsKey n ∧ allPairsKey n ≠ pairKey t0 t1 ∧ allPairsKey n ≠ pairKey t1 t0

/-- **createPair's target**, with `(t0, t1) = sortTokens tokenA tokenB`, `n = allPairs.length`:
* `tokenA = tokenB` reverts with `IDENTICAL_ADDRESSES`; else `t0 = 0` with `ZERO_ADDRESS`; else a
  nonzero `getPair[t0][t1]` with `PAIR_EXISTS`;
* a success made the `CREATE2` (salt `pairSalt t0 t1`; succeeded), then `initialize(t0, t1)` on
  `pair = create2Address factory salt initHash` (which has code; answered with success), and
  nothing else; `getPair[t0][t1] = getPair[t1][t0] = pair` (low 160 bits), `n < 2^64`,
  `allPairs.length = n + 1`, `allPairs[n] = pair`; logs `PairCreated(t0, t1, pair, n + 1)`;
  returns `pair`; no other slot changes. -/
def CreatePairTarget (env : Env) (W : World) (initHash : Nat) (st : Store) (a b : Nat) (r : Result) :
    Prop :=
  let t0 := (sortTokens a b).1
  let t1 := (sortTokens a b).2
  let salt := pairSalt t0 t1
  let pair := create2Address env.self salt initHash
  let n := st allPairsSlot
  (a = b → Reverts st (err "UniswapV2: IDENTICAL_ADDRESSES") r) ∧
  (a ≠ b → t0 = 0 → Reverts st (err "UniswapV2: ZERO_ADDRESS") r) ∧
  (a ≠ b → t0 ≠ 0 → st (pairKey t0 t1) % U160 ≠ 0 → Reverts st (err "UniswapV2: PAIR_EXISTS") r) ∧
  (r.success = true →
    (W.ans 0 (.create2 salt)).ok = true ∧ W.hasCode pair = true ∧ (W.ans 1 (initQ pair t0 t1)).ok = true ∧
    r.calls = [.create2 salt, initQ pair t0 t1] ∧
    st (pairKey t0 t1) % U160 = 0 ∧ n < 2 ^ 64 ∧
    r.storage (pairKey t0 t1) = setLow160 (st (pairKey t0 t1)) pair ∧
    r.storage (pairKey t1 t0) = setLow160 (st (pairKey t1 t0)) pair ∧
    r.storage allPairsSlot = n + 1 ∧
    r.storage (allPairsKey n) = setLow160 (st (allPairsKey n)) pair ∧
    FrameOutside st r.storage [pairKey t0 t1, pairKey t1 t0, allPairsSlot, allPairsKey n] ∧
    r.logs = [([pairCreatedTopic, t0, t1], be32 pair ++ be32 (n + 1))] ∧ r.output = be32 pair) ∧
  (r.success = false → r.storage = st ∧ r.logs = [] ∧ r.calls = [])

/-- **createPair's statement.** Premises: `ScopedSep (createPairFootprint t0 t1)`,
`ArrayApart t0 t1 allPairs.length`, and no code at address 0 (a failed `CREATE2` gives the pair
address 0, whose `initialize` must then revert); `initHash` is a parameter. -/
def CreatePairSpec : Prop :=
  ∀ env W initHash st a b, env.WF → env.callvalue = 0 → Words st → a < U160 → b < U160 →
    W.hasCode 0 = false →
    ScopedSep (createPairFootprint (sortTokens a b).1 (sortTokens a b).2) →
    ArrayApart (sortTokens a b).1 (sortTokens a b).2 (st allPairsSlot) →
    CreatePairTarget env W initHash st a b (createPairResult env W initHash st a b)

/-! ## setFeeTo(address) and setFeeToSetter(address) -/

/-- Only `feeToSetter` may write the address slot `k` (`feeTo` or `feeToSetter`). -/
def setterResult (env : Env) (st : Store) (k x : Nat) : Result := run st do
  nonpayable env
  let s ← sload feeToSetterSlot
  require (env.caller = s % U160) (err "UniswapV2: FORBIDDEN")
  sstoreAddr k x
  return []

def setFeeToResult (env : Env) (st : Store) (x : Nat) : Result := setterResult env st feeToSlot x
def setFeeToSetterResult (env : Env) (st : Store) (x : Nat) : Result := setterResult env st feeToSetterSlot x

/-- **The setters' target**: success iff the caller is `feeToSetter`; then the slot `k` holds `x`
(low 160 bits; upper 96 kept) and nothing else changes; no log, no return data, no request;
otherwise `UniswapV2: FORBIDDEN` and no change. -/
def SetterTarget (env : Env) (st : Store) (k x : Nat) (r : Result) : Prop :=
  (r.success = true ↔ env.caller = st feeToSetterSlot % U160) ∧
  (r.success = true → r.storage = upd st k (setLow160 (st k) x) ∧ r.logs = [] ∧ r.output = [] ∧
    r.calls = []) ∧
  (r.success = false → Reverts st (err "UniswapV2: FORBIDDEN") r)

/-- **setFeeTo's statement.** No hash premise. -/
def SetFeeToSpec : Prop :=
  ∀ env st x, env.WF → env.callvalue = 0 → Words st → x < U160 →
    SetterTarget env st feeToSlot x (setFeeToResult env st x)

/-- **setFeeToSetter's statement.** No hash premise. -/
def SetFeeToSetterSpec : Prop :=
  ∀ env st x, env.WF → env.callvalue = 0 → Words st → x < U160 →
    SetterTarget env st feeToSetterSlot x (setFeeToSetterResult env st x)

end SolidCore.Spec.UniswapV2.Specs.Factory
