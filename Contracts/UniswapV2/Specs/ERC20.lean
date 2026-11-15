import Contracts.UniswapV2.Specs.Common

/-!
# UniswapV2ERC20: transfer, approve, transferFrom, permit

Storage layout of the port's `UniswapV2ERC20` (and of the pair, which inherits it at the same
slots): `totalSupply` 0, `balanceOf` 1, `allowance` 2, `DOMAIN_SEPARATOR` 3, `nonces` 4 (the
constants `name`, `symbol`, `decimals` and `PERMIT_TYPEHASH` take no slot).

For each function: `…Result`, the sequential model (no hash premise); `…Target`, the
postcondition in the words of the storage before the call; `…Spec`, the statement to prove: on
every valid call (a well-formed frame with no value, clean arguments, a storage of words) whose
footprint premise holds, the model meets the target. A spec about SolidCore's runs is
`…Spec` with `…Result` replaced by the run (the E7 edge); none is proved here.

`transfer` is certified at the caller `0x2000` (`Contracts/UniswapV2/ERC20/Certified/Transfer.lean`,
`Slice.SeqPost` and `Slice.TargetPost`): `transferResult` and `TransferTarget` restate them for any
caller, unchanged otherwise, so the other functions and the pair can reuse them.
-/

namespace SolidCore.Spec.UniswapV2.Specs.ERC20

open SolidCore.Spec.UniswapV2.Specs SolidCore.Refinement.Generic

/-! ## Layout, events -/

abbrev totalSupplySlot : Nat := 0
abbrev balanceOfSlot : Nat := 1
abbrev allowanceSlot : Nat := 2
abbrev domainSeparatorSlot : Nat := 3
abbrev noncesSlot : Nat := 4

/-- The slot of `balanceOf[a]`. -/
def balKey (a : Nat) : Nat := solHash a balanceOfSlot
/-- The slot of `allowance[o][s]`. -/
def allowKey (o s : Nat) : Nat := solHash s (solHash o allowanceSlot)
/-- The slot of `nonces[o]`. -/
def nonceKey (o : Nat) : Nat := solHash o noncesSlot

/-- `Transfer(address,address,uint256)`. -/
def transferTopic : Nat := topicOf "Transfer(address,address,uint256)"
/-- `Approval(address,address,uint256)`. -/
def approvalTopic : Nat := topicOf "Approval(address,address,uint256)"
/-- `PERMIT_TYPEHASH`: keccak256 of the EIP-2612 `Permit` type. -/
def permitTypehash : Nat :=
  topicOf "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"

/-- The log `Transfer(f, t, v)`. -/
def transferLog (f t v : Nat) : List Nat × List Nat := ([transferTopic, f, t], be32 v)
/-- The log `Approval(o, s, v)`. -/
def approvalLog (o s v : Nat) : List Nat × List Nat := ([approvalTopic, o, s], be32 v)

/-- Every slot outside `ks` is as in `st`. -/
def FrameOutside (st st' : Store) (ks : List Nat) : Prop := ∀ n, (n % U256) ∉ ks → st' n = st n

/-! ## Shared steps (the source's internal functions) -/

/-- `_transfer(frm, dst, v)`: debit `frm`, then credit `dst` reading the debited state, then log. -/
def moveBalance (frm dst v : Nat) : M Unit := do
  let b ← sload (balKey frm)
  let b' ← sub b v
  sstore (balKey frm) b'
  let d ← sload (balKey dst)
  let d' ← add d v
  sstore (balKey dst) d'
  emit [transferTopic, frm, dst] (be32 v)

/-- `_mint(dst, v)`: `totalSupply += v`, then `balanceOf[dst] += v` (SafeMath), then
`Transfer(0, dst, v)`. -/
def mintLP (dst v : Nat) : M Unit := do
  let t ← sload totalSupplySlot
  let t' ← add t v
  sstore totalSupplySlot t'
  let b ← sload (balKey dst)
  let b' ← add b v
  sstore (balKey dst) b'
  emit [transferTopic, 0, dst] (be32 v)

/-- `_burn(frm, v)`: `balanceOf[frm] -= v`, then `totalSupply -= v` (SafeMath), then
`Transfer(frm, 0, v)`. -/
def burnLP (frm v : Nat) : M Unit := do
  let b ← sload (balKey frm)
  let b' ← sub b v
  sstore (balKey frm) b'
  let t ← sload totalSupplySlot
  let t' ← sub t v
  sstore totalSupplySlot t'
  emit [transferTopic, frm, 0] (be32 v)

/-- The valid arguments: clean addresses and words. -/
def Clean (addrs words : List Nat) : Prop := (∀ a ∈ addrs, a < U160) ∧ ∀ w ∈ words, w < U256

/-- The valid calls' common part: a well-formed frame without value, a storage of words. -/
def ValidCall (env : Env) (st : Store) : Prop := env.WF ∧ env.callvalue = 0 ∧ Words st

/-! ## transfer(address to, uint256 value) returns (bool) -/

/-- The sequential model (`Slice.SeqPost` for any caller). -/
def transferResult (env : Env) (st : Store) (dst v : Nat) : Result := run st do
  nonpayable env
  moveBalance env.caller dst v
  return be32 1

/-- **transfer's target** (`Slice.TargetPost` for any caller): `caller ≠ to` succeeds iff the
caller's balance covers `v` and `to`'s does not overflow, then debits and credits; `caller = to`
succeeds iff the balance covers `v` and changes nothing; a success logs `Transfer(caller, to, v)`,
returns `true`, makes no request and writes no slot outside the two balances; a failure reverts
with SafeMath's data and changes nothing. -/
def TransferTarget (env : Env) (st : Store) (dst v : Nat) (r : Result) : Prop :=
  let c := env.caller
  (c ≠ dst →
    (r.success = true ↔ v ≤ st (balKey c) ∧ st (balKey dst) + v < U256) ∧
    (r.success = true → r.storage (balKey c) = st (balKey c) - v ∧
      r.storage (balKey dst) = st (balKey dst) + v)) ∧
  (c = dst → (r.success = true ↔ v ≤ st (balKey c)) ∧ (r.success = true → r.storage = st)) ∧
  (r.success = true → r.logs = [transferLog c dst v] ∧ r.output = be32 1 ∧ r.calls = [] ∧
    FrameOutside st r.storage [balKey c, balKey dst]) ∧
  (r.success = false → r.storage = st ∧ r.logs = [] ∧
    r.output = if v ≤ st (balKey c) then err "ds-math-add-overflow" else err "ds-math-sub-underflow")

/-- The footprint of transfer: the caller's and the recipient's balance slots. -/
def transferFootprint (c dst : Nat) : List (List Nat) := SolidCore.Spec.transferFootprint balanceOfSlot c dst

/-- **transfer's statement.** Premise: `ScopedSep (transferFootprint caller to)`. -/
def TransferSpec : Prop :=
  ∀ env st dst v, ValidCall env st → Clean [dst] [v] → ScopedSep (transferFootprint env.caller dst) →
    TransferTarget env st dst v (transferResult env st dst v)

/-! ## approve(address spender, uint256 value) returns (bool) -/

/-- The sequential model: `allowance[caller][spender] = value`, `Approval(caller, spender, value)`,
returns `true`. -/
def approveResult (env : Env) (st : Store) (sp v : Nat) : Result := run st do
  nonpayable env
  sstore (allowKey env.caller sp) v
  emit [approvalTopic, env.caller, sp] (be32 v)
  return be32 1

/-- **approve's target**: always succeeds; the one slot `allowance[caller][spender]` becomes
`value` and nothing else changes (stated at the slot, so no hash premise); logs
`Approval(caller, spender, value)`; returns `true`. -/
def ApproveTarget (env : Env) (st : Store) (sp v : Nat) (r : Result) : Prop :=
  r.success = true ∧ r.storage = upd st (allowKey env.caller sp) v ∧
    r.logs = [approvalLog env.caller sp v] ∧ r.output = be32 1 ∧ r.calls = []

/-- **approve's statement.** No hash premise. -/
def ApproveSpec : Prop :=
  ∀ env st sp v, ValidCall env st → Clean [sp] [v] → ApproveTarget env st sp v (approveResult env st sp v)

/-! ## transferFrom(address from, address to, uint256 value) returns (bool) -/

/-- The sequential model (`Nested.transferFromResult` for any caller): unless
`allowance[from][caller]` is `type(uint256).max`, it is decreased by `value` (SafeMath); then
`_transfer(from, to, value)`; returns `true`. -/
def transferFromResult (env : Env) (st : Store) (frm dst v : Nat) : Result := run st do
  nonpayable env
  let a ← sload (allowKey frm env.caller)
  if a ≠ umax then
    let a' ← sub a v
    sstore (allowKey frm env.caller) a'
  moveBalance frm dst v
  return be32 1

/-- **transferFrom's target**, with `a = allowance[from][caller]`, `b = balanceOf[from]`,
`d = balanceOf[to]` before the call: success iff (`a` is infinite or covers `value`), `b` covers
`value` and (`from = to` or `d + value` does not overflow); then a finite allowance drops by
`value`, an infinite one stays; `from ≠ to` debits and credits; `from = to` leaves the balance;
logs `Transfer(from, to, value)`, returns `true`, writes nothing else; a failure reverts with
SafeMath's data (allowance first, then balance, then overflow) and changes nothing. -/
def TransferFromTarget (env : Env) (st : Store) (frm dst v : Nat) (r : Result) : Prop :=
  let a := st (allowKey frm env.caller)
  let b := st (balKey frm)
  let d := st (balKey dst)
  (r.success = true ↔ (a = umax ∨ v ≤ a) ∧ v ≤ b ∧ (frm = dst ∨ d + v < U256)) ∧
  (r.success = true →
    r.storage (allowKey frm env.caller) = (if a = umax then a else a - v) ∧
    (frm ≠ dst → r.storage (balKey frm) = b - v ∧ r.storage (balKey dst) = d + v) ∧
    (frm = dst → r.storage (balKey frm) = b) ∧
    FrameOutside st r.storage [allowKey frm env.caller, balKey frm, balKey dst] ∧
    r.logs = [transferLog frm dst v] ∧ r.output = be32 1 ∧ r.calls = []) ∧
  (r.success = false → r.storage = st ∧ r.logs = [] ∧
    r.output = if (a = umax ∨ v ≤ a) ∧ v ≤ b then err "ds-math-add-overflow"
      else err "ds-math-sub-underflow")

/-- **transferFrom's statement.** Premise: `ScopedSep (transferFromFootprint caller from to)`, the
preimages of `allowance[from][caller]` (inner and outer), `balanceOf[from]` and `balanceOf[to]`
(Verify/Spec/HashScopeNested.lean). -/
def TransferFromSpec : Prop :=
  ∀ env st frm dst v, ValidCall env st → Clean [frm, dst] [v] →
    ScopedSep (SolidCore.Spec.HashScopeNested.transferFromFootprint env.caller frm dst) →
    TransferFromTarget env st frm dst v (transferFromResult env st frm dst v)

/-! ## permit(owner, spender, value, deadline, v, r, s) -/

/-- The EIP-712 digest the source signs over: `keccak256(0x1901 ‖ DOMAIN_SEPARATOR ‖
keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, value, nonce, deadline)))`. -/
def permitDigest (ds owner sp v n deadline : Nat) : Nat :=
  keccak ([0x19, 0x01] ++ be32 ds ++
    be32 (keccak (be32 permitTypehash ++ be32 owner ++ be32 sp ++ be32 v ++ be32 n ++ be32 deadline)))

/-- The sequential model: `deadline >= block.timestamp` or `UniswapV2: EXPIRED`; the nonce is read
and incremented (checked: 0x11 at the maximum); the signer `ecrecover(digest, v, r, s)` must be
nonzero and `owner` (`UniswapV2: INVALID_SIGNATURE`); then `_approve(owner, spender, value)`. -/
def permitResult (env : Env) (W : World) (st : Store) (owner sp v deadline sv sr ss : Nat) : Result :=
  run st do
    nonpayable env
    require (env.timestamp ≤ deadline) (err "UniswapV2: EXPIRED")
    let ds ← sload domainSeparatorSlot
    let n ← sload (nonceKey owner)
    let n' ← inc n
    sstore (nonceKey owner) n'
    let signer := W.ecrecover (permitDigest ds owner sp v n deadline) sv sr ss
    require (signer ≠ 0 ∧ signer = owner) (err "UniswapV2: INVALID_SIGNATURE")
    sstore (allowKey owner sp) v
    emit [approvalTopic, owner, sp] (be32 v)
    return []

/-- **permit's target**, with `n = nonces[owner]` and `signer` the precompile's answer on the digest
of the storage before the call: success iff `timestamp ≤ deadline`, `n < type(uint256).max` and
`signer = owner ≠ 0`; then `nonces[owner] = n + 1`, `allowance[owner][spender] = value`, nothing
else, `Approval(owner, spender, value)`, no return data; a failure reverts with `EXPIRED`, then the
increment's panic, then `INVALID_SIGNATURE`, and changes nothing. -/
def PermitTarget (env : Env) (W : World) (st : Store) (owner sp v deadline sv sr ss : Nat)
    (r : Result) : Prop :=
  let n := st (nonceKey owner)
  let signer := W.ecrecover (permitDigest (st domainSeparatorSlot) owner sp v n deadline) sv sr ss
  (r.success = true ↔ env.timestamp ≤ deadline ∧ n < umax ∧ signer ≠ 0 ∧ signer = owner) ∧
  (r.success = true →
    r.storage (nonceKey owner) = n + 1 ∧ r.storage (allowKey owner sp) = v ∧
    FrameOutside st r.storage [nonceKey owner, allowKey owner sp] ∧
    r.logs = [approvalLog owner sp v] ∧ r.output = [] ∧ r.calls = []) ∧
  (r.success = false → r.storage = st ∧ r.logs = [] ∧
    r.output = if ¬ env.timestamp ≤ deadline then err "UniswapV2: EXPIRED"
      else if n = umax then panicData 0x11 else err "UniswapV2: INVALID_SIGNATURE")

/-- The footprint of permit: `nonces[owner]` and `allowance[owner][spender]` (inner and outer). -/
def permitFootprint (owner sp : Nat) : List (List Nat) :=
  pre owner noncesSlot :: SolidCore.Spec.HashScopeNested.nestedFootprint allowanceSlot owner sp

/-- **permit's statement.** Premise: `ScopedSep (permitFootprint owner spender)`; `v` a clean
`uint8`. -/
def PermitSpec : Prop :=
  ∀ env W st owner sp v deadline sv sr ss, ValidCall env st → Clean [owner, sp] [v, deadline, sr, ss] →
    sv < 256 → ScopedSep (permitFootprint owner sp) →
    PermitTarget env W st owner sp v deadline sv sr ss (permitResult env W st owner sp v deadline sv sr ss)

end SolidCore.Spec.UniswapV2.Specs.ERC20
