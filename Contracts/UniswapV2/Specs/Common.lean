import Verify.Spec.HashScope
import Verify.Spec.HashScopeNested

/-!
# Uniswap V2 port: the shared vocabulary of the function specifications

Statements only: definitions and `Prop`s, no proofs (docs/specs/UNISWAPV2_SPECS.md lists every
statement, its premises and where it is weaker than the source, for review). Nothing here depends
on the port's code (v2-core is GPL-3.0 and not committed): the specifications are written from
the port's behaviour, in the style of the certified transfer slice
(`Contracts/UniswapV2/ERC20/Slice/Post.lean`):

* **sequential models** (`…Result`): the source's storage updates in source order, each read
  seeing the writes before it, so any aliasing of slots is the source's and needs no hash premise
  (as `Slice.SeqPost` and `Nested.transferFromResult`);
* **target statements** (`…Target`, `…Spec`): the same in the words of the storage before the
  call, key by key, under keccak256 separated on the call's footprint only (`ScopedSep`,
  Verify/Spec/HashScope.lean), never over all keys (as `Slice.TargetPost`).

## The model of one call

* `Env`: the frame: `msg.sender`, `address(this)`, `block.timestamp`, `block.chainid`,
  `msg.value`. `SolarTV.Call` has no caller field and every certified edge fixes the caller to
  `0x2000` (`Generic.callerWord`); these statements take the caller as a parameter, so their
  instance at today's edges is `caller = 0x2000`.
* `Store`: the contract's storage as words by slot, as `SolarTV.Observable.storage`.
* `World`: what the rest of the chain answers. The `i`-th external request of the call (`Req`) is
  answered by `ans i req`; `hasCode` is `extcodesize > 0`; `ecrecover` is the precompile.
  **The world never writes this contract's storage**: `World` has no storage component, so no
  answer can change the calling contract's slots. This is the no-reentrant-write premise of every
  function that makes external calls (as `PairFramed`, Contracts/UniswapV2/PairSpec/Inputs.lean),
  built into the model and flagged at each function in the review list.
* `Result`: `SolarTV.Observable`'s four fields and the external requests the call made, in order
  (`calls`, empty on a revert, which rolls the callees' effects back with the caller's).
* `M`: a state monad over storage, logs and requests that fails with revert data; `run` turns a
  program into a `Result`, a revert into no change and no log.
-/

namespace SolidCore.Spec.UniswapV2.Specs

open SolidCore.Refinement.Generic

/-! ## Words and bytes -/

/-- `2 ^ 256`. -/
abbrev U256 : Nat := 2 ^ 256
/-- `2 ^ 160`: one past the largest address. -/
abbrev U160 : Nat := 2 ^ 160
/-- `2 ^ 112`: one past the largest `uint112`. -/
abbrev U112 : Nat := 2 ^ 112
/-- `2 ^ 32`: one past the largest `uint32`. -/
abbrev U32 : Nat := 2 ^ 32
/-- `type(uint256).max`. -/
abbrev umax : Nat := 2 ^ 256 - 1

/-- `w` as `n` big-endian bytes (its low `8 n` bits). -/
def be (n w : Nat) : List Nat := (List.range n).map fun i => w / 256 ^ (n - 1 - i) % 256

/-- A word's 32 bytes, big-endian (`Slice.be32`). -/
def be32 (w : Nat) : List Nat := be 32 w

/-- The word of big-endian bytes. -/
def wordOf (bs : List Nat) : Nat := bs.foldl (fun acc b => acc * 256 + b) 0

/-- A string's UTF-8 bytes. -/
def utf8 (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)

/-- keccak256 of a byte list, as a word. -/
abbrev keccak (bs : List Nat) : Nat := SolidCore.Spec.keccakWord bs

/-- The 4-byte selector of a function signature. -/
def selectorOf (sig : String) : Nat := keccak (utf8 sig) / 2 ^ 224

/-- The topic of an event signature. -/
def topicOf (sig : String) : Nat := keccak (utf8 sig)

/-- ABI call data of `sig` with static word arguments `args`. -/
def calldata (sig : String) (args : List Nat) : List Nat := be 4 (selectorOf sig) ++ args.flatMap be32

/-- `bs` padded with zero bytes to a whole number of words. -/
def padWords (bs : List Nat) : List Nat := bs ++ List.replicate ((32 - bs.length % 32) % 32) 0

/-- The revert data of `Error(msg)`: the selector `0x08c379a0`, the offset `0x20`, the length
and the message padded to whole words (for a message of 1 to 32 bytes, `Slice.errorData`). -/
def errorData (msg : List Nat) : List Nat :=
  [0x08, 0xc3, 0x79, 0xa0] ++ be32 0x20 ++ be32 msg.length ++ padWords msg

/-- The revert data of `require(_, s)`. -/
def err (s : String) : List Nat := errorData (utf8 s)

/-- The revert data of `Panic(code)` (0x11 arithmetic overflow, 0x12 division by zero, 0x41 too
large an array). -/
def panicData (code : Nat) : List Nat := [0x4e, 0x48, 0x7b, 0x71] ++ be32 code

/-! ## The frame, the storage, the world -/

/-- The frame a call runs in. -/
structure Env where
  /-- `msg.sender`. -/
  caller : Nat
  /-- `address(this)`. -/
  self : Nat
  /-- `block.timestamp`. -/
  timestamp : Nat
  /-- `block.chainid`. -/
  chainid : Nat
  /-- `msg.value`. -/
  callvalue : Nat

/-- A well-formed frame: addresses below `2 ^ 160`, words below `2 ^ 256`. -/
def Env.WF (e : Env) : Prop :=
  e.caller < U160 ∧ e.self < U160 ∧ e.timestamp < U256 ∧ e.chainid < U256 ∧ e.callvalue < U256

/-- Storage: a word per slot. -/
abbrev Store := Nat → Nat

/-- A storage of words indexed modulo `2 ^ 256` (as `SolarTV.slotValue` reads one): every slot
holds a word, and slot `k` is slot `k % 2 ^ 256`. -/
def Words (st : Store) : Prop := ∀ k, st k < U256 ∧ st (k % U256) = st k

/-- The storage `s` with the slot `k` (a word) set to `x` (`Slice.upd`). -/
def upd (s : Store) (k x : Nat) : Store := fun n => if n % U256 = k then x else s n

/-- An external request: a message call with no value, or the `CREATE2` of the pair's init code
with a salt. -/
inductive Req where
  | call (target : Nat) (data : List Nat)
  | create2 (salt : Nat)

/-- An answer: the success flag and the return (or revert) data. A `CREATE2` succeeds or fails;
its data is unused. -/
structure Ans where
  ok : Bool
  ret : List Nat

/-- The rest of the chain, as the call sees it. -/
structure World where
  /-- The answer to the `i`-th external request of the call. -/
  ans : Nat → Req → Ans
  /-- `extcodesize(a) > 0`. -/
  hasCode : Nat → Bool
  /-- The `ecrecover` precompile: the signer of `digest` under `(v, r, s)`, or 0. -/
  ecrecover : Nat → Nat → Nat → Nat → Nat

/-- An answer that returns the word `w`: success with at least 32 bytes, the first word `w`. -/
def ReturnsWord (a : Ans) (w : Nat) : Prop :=
  a.ok = true ∧ 32 ≤ a.ret.length ∧ wordOf (a.ret.take 32) = w

/-- What a call observes: `SolarTV.Observable`'s fields and the external requests, in order. -/
structure Result where
  success : Bool
  output : List Nat
  logs : List (List Nat × List Nat)
  storage : Store
  calls : List Req

/-! ## The sequential model -/

/-- The state of a running call. -/
structure Frame where
  st : Store
  logs : List (List Nat × List Nat)
  calls : List Req

/-- A program of the model: reads and writes storage, logs, makes requests, or reverts with data. -/
abbrev M := StateT Frame (Except (List Nat))

/-- Run a program from the storage `st`: success with its output, logs, storage and requests; a
revert with its data, no log, the storage it started with and no request. -/
def run (st : Store) (m : M (List Nat)) : Result :=
  match m.run ⟨st, [], []⟩ with
  | .ok (out, f) => ⟨true, out, f.logs, f.st, f.calls⟩
  | .error d => ⟨false, d, [], st, []⟩

/-- Revert with the data `d`. -/
def revert {α : Type} (d : List Nat) : M α := throw d

/-- `require(c, …)` with the revert data `d`. -/
def require (c : Prop) [Decidable c] (d : List Nat) : M Unit := if c then pure () else throw d

/-- Read a slot. -/
def sload (k : Nat) : M Nat := do return (← get).st k

/-- Write a slot. -/
def sstore (k x : Nat) : M Unit := modify fun f => { f with st := upd f.st k x }

/-- The word `w` with its low 160 bits set to the address `a` and its upper 96 kept: Solidity's
masked update of an address alone in its slot. -/
def setLow160 (w a : Nat) : Nat := w / U160 * U160 + a

/-- Write an address into a slot it occupies alone at offset 0 (`setLow160`). -/
def sstoreAddr (k a : Nat) : M Unit := do
  let w ← sload k
  sstore k (setLow160 w a)

/-- Log `topics` with `data`. -/
def emit (topics data : List Nat) : M Unit :=
  modify fun f => { f with logs := f.logs ++ [(topics, data)] }

/-- Make the next external request and take the world's answer to it. -/
def request (W : World) (r : Req) : M Ans := do
  let f ← get
  set { f with calls := f.calls ++ [r] }
  return W.ans f.calls.length r

/-- A function that accepts no value: `msg.value ≠ 0` reverts with no data. -/
def nonpayable (env : Env) : M Unit := require (env.callvalue = 0) []

/-! ## Arithmetic as the source performs it -/

/-- SafeMath's `add`: reverts with `ds-math-add-overflow` from `2 ^ 256` on. -/
def add (x y : Nat) : M Nat :=
  if x + y < U256 then pure (x + y) else revert (err "ds-math-add-overflow")

/-- SafeMath's `sub`: reverts with `ds-math-sub-underflow` below zero. -/
def sub (x y : Nat) : M Nat :=
  if y ≤ x then pure (x - y) else revert (err "ds-math-sub-underflow")

/-- SafeMath's `mul`: reverts with `ds-math-mul-overflow` from `2 ^ 256` on. -/
def mul (x y : Nat) : M Nat :=
  if x * y < U256 then pure (x * y) else revert (err "ds-math-mul-overflow")

/-- Checked `/`: division by zero panics with 0x12. -/
def div (x y : Nat) : M Nat := if y = 0 then revert (panicData 0x12) else pure (x / y)

/-- Checked `x++`: panics with 0x11 at `type(uint256).max`. -/
def inc (x : Nat) : M Nat := if x + 1 < U256 then pure (x + 1) else revert (panicData 0x11)

/-! ## External calls as the source makes them -/

/-- A high-level call returning one word (`IERC20(t).balanceOf(…)`): a failure reverts with the
callee's revert data verbatim; return data shorter than a word reverts with no data. No
`extcodesize` check (the call decodes return data). -/
def callWord (W : World) (target : Nat) (data : List Nat) : M Nat := do
  let a ← request W (.call target data)
  if a.ok then
    if 32 ≤ a.ret.length then pure (wordOf (a.ret.take 32)) else revert []
  else revert a.ret

/-- A high-level call returning an address (`factory.feeTo()`): as `callWord`, and a word of
`2 ^ 160` or more reverts with no data. -/
def callAddress (W : World) (target : Nat) (data : List Nat) : M Nat := do
  let w ← callWord W target data
  if w < U160 then pure w else revert []

/-- A high-level call with no return value (`initialize`, `uniswapV2Call`): a target without code
reverts with no data before the call; a failure reverts with the callee's revert data. -/
def callUnit (W : World) (target : Nat) (data : List Nat) : M Unit := do
  if W.hasCode target then
    let a ← request W (.call target data)
    if a.ok then pure () else revert a.ret
  else revert []

/-- `transfer(address,uint256)`'s call data. -/
def transferData (dst v : Nat) : List Nat := calldata "transfer(address,uint256)" [dst, v]

/-- The pair's `_safeTransfer(token, to, value)`: a low-level call of `transfer(to, value)`;
success with empty return data or the word 1 passes; a failure or the word 0 reverts with
`UniswapV2: TRANSFER_FAILED`; return data of 1 to 31 bytes or a word above 1 reverts with no data
(the ABI decoder of `bool`). No `extcodesize` check (a low-level call). -/
def safeTransfer (W : World) (token dst v : Nat) : M Unit := do
  let a ← request W (.call token (transferData dst v))
  if a.ok then
    if a.ret.length = 0 then pure ()
    else if a.ret.length < 32 then revert []
    else
      let w := wordOf (a.ret.take 32)
      if w = 1 then pure ()
      else if w = 0 then revert (err "UniswapV2: TRANSFER_FAILED")
      else revert []
  else revert (err "UniswapV2: TRANSFER_FAILED")

/-- An answer to a token's `transfer` that `safeTransfer` accepts. -/
def TransferAccepted (a : Ans) : Prop :=
  a.ok = true ∧ (a.ret.length = 0 ∨ (32 ≤ a.ret.length ∧ wordOf (a.ret.take 32) = 1))

/-! ## Hash premises -/

/-- keccak256 separated on the footprint `L` (`SolidCore.Spec.ScopedSep`): injective on `L`,
every image at least `2 ^ 128`. Satisfiable for every finite `L`
(`SolidCore.Spec.exists_separatedBy`). -/
abbrev ScopedSep (L : List (List Nat)) : Prop := SolidCore.Spec.ScopedSep L

/-- The preimage of `m[a]`'s slot, for a mapping at slot `m`. -/
abbrev pre (a m : Nat) : List Nat := SolidCore.Spec.TrustedBase.mappingPreimage a m


end SolidCore.Spec.UniswapV2.Specs
