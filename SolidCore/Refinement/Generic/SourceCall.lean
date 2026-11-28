import SolidCore.Refinement.Generic.SourceStmt

/-!
# Functions and the dispatcher of the fragment

`eraseFn` erases a SolidCore function of the fragment to the `Tree` of one external call of it.
Its parameters are words: a `uint256` with a `uint b` ABI cleanup, `0 < b ≤ 256`, a `uint256` with an
`enum m` cleanup (an enum parameter, whose largest member is `m`), an `address` with no cleanup,
as SolidCore's type checker gives a Solidity `address` parameter, or a `bool` with no cleanup; each
has a bound (`paramWidth`: the largest word SolidCore's decoder accepts for it: `2 ^ b - 1`, `m`,
`2 ^ 160 - 1` or 1). Its returns are `uint256`, `address` or `bool`
words, and none of its bindings is a storage reference. The tree is the argument checks
(`paramGuards`: a word above the bound `m < 2 ^ 256 - 1` of its parameter reverts with empty
data, as SolidCore's decoder, its address and bool checks, or its `uint b` and `enum m` cleanups, and solar's `lower-abi`
do), then the body's branch tree run from `initState`, with each leaf turned into the call's end
by `leafTree`: the returned words ABI-encoded with the body's storage writes and logs, or a
revert's data (empty, `Panic(code)` or `Error(msg)`) with neither.

Past the argument checks every argument word is at most its bound, which the facts `argFacts` record
(`gt (arg i) m` taken as zero). The erasure reads them through the `EraseEnv`'s
`facts` and `leafTree` through its own: a returned `address` word must be below `2 ^ 160` and a
`bool` word at most 1 on every call (`retOk`: its `bound` on the facts), as SolidCore's encoder
asks, so an `address` parameter, `msg.sender`, a masked storage read or a comparison returns
as it is.
-/

namespace SolidCore.Refinement.Generic
open SolidCore.Solidity.Source

/-- A return binding of the fragment: a `uint256`, an `address` or a `bool`, not a storage
reference. -/
def wordBinding (b : BindingDecl) : Bool :=
  (match b.ty with | .uint256 => true | .address => true | .bool => true | _ => false) &&
    !b.isStorageRef

/-- The bound of the argument word of a parameter of the fragment, from its binding and its ABI
cleanup: the largest word SolidCore's decoder accepts for it. `2 ^ b - 1` for a `uint256` with the
cleanup `uint b`, `0 < b ≤ 256`; `m` for a `uint256` with the cleanup `enum m` (an enum
parameter whose largest member is `m`); `2 ^ 160 - 1` for an `address` and 1 for a `bool`, each with
no cleanup; `2 ^ 256 - 1` (no check) for an `int256` with the cleanup `int 256` and for a `bytes32`,
which SolidCore holds as typed values (`tagOf`); `wordSize + b` for a signed `b`-bit parameter, an
`int256` with the cleanup `int b`, `0 < b < 256`, whose word must be its own sign extension from
bit `b - 1` (`sextGuard`): a number at or above `wordSize` names that check rather than a bound,
so every parameter keeps one number and the checks one list. An enum of one member (`m = 0`) has
the bound 0: past its check its argument word is 0, which `WExpr.simp` folds from the path's facts
as solar's MIR returns the constant. -/
def paramWidthT (p : BindingDecl) (c : AbiCleanup) : Option Nat :=
  if p.isStorageRef then none
  else
    match p.ty, c with
    | .uint256, .uint b => if 0 < b ∧ b ≤ 256 then some (2 ^ b - 1) else none
    | .uint256, .enum m => if m < wordSize then some m else none
    | .address, .none => some (2 ^ 160 - 1)
    | .bool, .none => some 1
    | .int256, .int 256 => some (2 ^ 256 - 1)
    | .int256, .int b => if 0 < b ∧ b < 256 then some (wordSize + b) else none
    | .fixedBytes 32, .none => some (2 ^ 256 - 1)
    | .tuple [.uint256], .tuple [.uint 256] => some (2 ^ 256 - 1)
    | _, _ => none

/-- The tag SolidCore holds a parameter of type `ty` by: a signed word for an `int256`, a
`bytes32` for a `bytes32`, and a word otherwise. -/
def tagOf : Ty → Tag
  | .int256 => .int
  | .fixedBytes 32 => .bytes32
  | .tuple [.uint256] => .tup1
  | _ => .word

/-- The tags of the parameters SolidCore holds as typed values, by name. -/
def paramTags : List BindingDecl → Tags
  | [] => []
  | p :: ps => if tagOf p.ty = .word then paramTags ps else (p.name, tagOf p.ty) :: paramTags ps

/-- The tags of a call's parameters and returns SolidCore holds as typed values. -/
def fnTags (fn : FunctionDef) : Tags := paramTags (fn.params ++ fn.returns)

/-- Every parameter's and return's name has its type's tag: no typed binding shares its name with
another binding of the call. -/
def tagsOk (fn : FunctionDef) : Bool :=
  (fn.params ++ fn.returns).all (fun p => (fnTags fn).get p.name == tagOf p.ty)

/-- A return binding of the generic source stage: a word return, an `int256` or a `bytes32`, not a
storage reference. -/
def retBinding (b : BindingDecl) : Bool :=
  (match b.ty with
    | .uint256 => true | .address => true | .bool => true | .int256 => true | .fixedBytes 32 => true
    | _ => false) &&
    !b.isStorageRef

/-- The bound of a parameter the fragment holds as a word: `paramWidthT` on a parameter whose type's
tag is the word tag. The loop routes take only these. -/
def paramWidth (p : BindingDecl) (c : AbiCleanup) : Option Nat :=
  if tagOf p.ty = .word then paramWidthT p c else none

/-- The bounds of the parameters of the fragment, one per parameter and its ABI cleanup (the name
is kept from when every bound was `2 ^ w - 1` for a width `w`), every parameter a word. -/
def widthsOf : List BindingDecl → List AbiCleanup → Option (List Nat)
  | [], [] => some []
  | p :: ps, c :: cs => do
    let w ← paramWidth p c
    let ws ← widthsOf ps cs
    some (w :: ws)
  | _, _ => none

/-- The bounds of the parameters of the generic source stage, typed parameters included. -/
def widthsOfT : List BindingDecl → List AbiCleanup → Option (List Nat)
  | [], [] => some []
  | p :: ps, c :: cs => do
    let w ← paramWidthT p c
    let ws ← widthsOfT ps cs
    some (w :: ws)
  | _, _ => none

/-- The checks of the argument words from parameter `i` on, given their bounds: a word of a
parameter of bound `m < 2 ^ 256 - 1` above `m` reverts with empty data, and so does a word of a
signed `b`-bit parameter (`m = wordSize + b`) that is not its own sign extension. -/
def paramGuards : List Nat → Nat → Tree → Tree
  | [], _, t => t
  | m :: ms, i, t =>
    if m < wordSize - 1 then
      .ite (.bin .gt (.arg i) (.lit m)) (.halt false [] [] []) (paramGuards ms (i + 1) t)
    else if 0 < m - wordSize ∧ m - wordSize < 256 then
      .ite (sextGuard (m - wordSize) (.arg i)) (.halt false [] [] []) (paramGuards ms (i + 1) t)
    else paramGuards ms (i + 1) t

/-- What the argument checks from parameter `i` on leave known: each word of a parameter of
bound `m < 2 ^ 256 - 1` is at most `m`. -/
def argFacts : List Nat → Nat → Facts
  | [], _ => []
  | m :: ms, i =>
    if m < wordSize - 1 then (.bin .gt (.arg i) (.lit m), false) :: argFacts ms (i + 1)
    else argFacts ms (i + 1)

/-- The parameters as locals: parameter `i` holds argument word `i`. -/
def paramLocals : List BindingDecl → Nat → Locals
  | [], _ => []
  | p :: ps, i => (p.name, .arg i) :: paramLocals ps (i + 1)

/-- The state a call of `fn` starts in: one scope with its parameters and its returns at zero,
no writes and no logs. -/
def initState (fn : FunctionDef) : SymState :=
  { scopes := [paramLocals fn.params 0 ++ fn.returns.map (fun r => (r.name, .lit 0))]
    writes := []
    logs := []
    tags := fnTags fn
    next := some 0 }

/-- A returned word SolidCore's encoder takes for its type on every call the facts hold on: any
word for a `uint256`, one below `2 ^ 160` for an `address`, at most 1 for a `bool`. -/
def retOk (K : Facts) (ty : Ty) (w : WExpr) : Bool :=
  match ty with
  | .uint256 => true
  | .address => decide (bound K w < 2 ^ 160)
  | .bool => decide (bound K w ≤ 1)
  | _ => false

/-- A returned word of tag `t` SolidCore's encoder takes for its return's type: a word as `retOk`
says, and a signed word for an `int256`. -/
def retOkT (K : Facts) (ty : Ty) : Tag → WExpr → Bool
  | .word, w => retOk K ty w
  | .int, _ => match ty with | .int256 => true | _ => false
  | .bytes32, _ => match ty with | .fixedBytes 32 => true | _ => false
  | .sref _, _ => false
  | .sptr _, _ => false
  | .mref, _ => false
  | .tup1, _ => false

/-- Every returned word is one SolidCore's encoder takes for its return's type. -/
def retsOk (K : Facts) : List BindingDecl → List WExpr → Bool
  | [], [] => true
  | r :: rs, w :: ws => retOk K r.ty w && retsOk K rs ws
  | _, _ => false

/-- Every returned word, by its tag (a word past the tags), is one SolidCore's encoder takes for
its return's type. -/
def retsOkT (K : Facts) : List BindingDecl → List Tag → List WExpr → Bool
  | rs, [], ws => retsOk K rs ws
  | r :: rs, t :: ts, w :: ws => retOkT K r.ty t w && retsOkT K rs ts ws
  | _, _ :: _, _ => false

/-- The bytes of SolidCore's `Error(msg)` revert data: the selector `0x08c379a0` and the ABI
encoding of the message, when every byte is one. -/
def errorBytes (msg : String) : Option (List OByte) :=
  match ABI.encodeValues? [.bytesCalldata] [.bytes (ABI.stringBytes msg)] with
  | some p =>
    let bs := ABI.encodeSelector ABI.errorSelector ++ p
    if bs.all (· < 256) then some (bs.map .lit) else none
  | none => none

/-- The word of a named return: a local the state holds as a word or as a `bytes32`. -/
def SymState.retW? (S : SymState) (x : String) : Option WExpr :=
  if S.tags.get x = .word ∨ S.tags.get x = .bytes32 then Scopes.get? S.scopes x else none

/-- How a call ends, from how its body ends: the returned words, ABI-encoded, or the named
returns when the body falls through or returns nothing, with the body's writes and logs; a
revert's data, with no writes and no logs. -/
def leafTree (fn : FunctionDef) (K : Facts) : Leaf → Option Tree
  | .normal S => do
    let ws ← fn.returns.mapM fun r => S.retW? r.name
    if retsOkT K fn.returns (fn.returns.map fun r => S.tags.get r.name) ws then
      some (.halt true (ws.flatMap wordOBytes) S.writes S.logs)
    else none
  | .returned S vs ts =>
    if vs = [] then do
      let ws ← fn.returns.mapM fun r => S.retW? r.name
      if retsOkT K fn.returns (fn.returns.map fun r => S.tags.get r.name) ws then
        some (.halt true (ws.flatMap wordOBytes) S.writes S.logs)
      else none
    else if retsOkT K fn.returns ts vs then
      some (.halt true (vs.flatMap wordOBytes) S.writes S.logs)
    else none
  | .reverted .empty => some (.halt false [] [] [])
  | .reverted (.panic c) => some (.halt false (panicBytes c) [] [])
  | .reverted (.error m) => (errorBytes m).map fun bs => .halt false bs [] []

/-- The call's tree from its body's branch tree. -/
def brTree (fn : FunctionDef) (K : Facts) : Br → Option Tree
  | .leaf l => leafTree fn K l
  | .ite c t e => do
    let t' ← brTree fn K t
    let e' ← brTree fn K e
    some (.ite c t' e')

/-- The erasure of an external call of `fn` in the contract `E` describes: its argument checks,
then its body run with fuel `fuel`, knowing the facts the checks leave. -/
def eraseFn (E : EraseEnv) (fuel : Nat) (fn : FunctionDef) : Option Tree :=
  match widthsOfT fn.params fn.paramAbiCleanups with
  | none => none
  | some ws =>
    if fn.returns.all retBinding && tagsOk fn then do
      let b ← eraseStmt { E with facts := argFacts ws 0 } fuel fn.body (initState fn)
      let t ← brTree fn (argFacts ws 0) b
      some (paramGuards ws 0 t)
    else none

end SolidCore.Refinement.Generic
