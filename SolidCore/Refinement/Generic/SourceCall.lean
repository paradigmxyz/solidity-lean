import SolidCore.Refinement.Generic.SourceStmt

/-!
# Functions and the dispatcher of the fragment

`eraseFn` erases a SolidCore function of the fragment to the `Tree` of one external call of it.
Its parameters are words: a `uint256` with a `uint b` ABI cleanup, `0 < b ≤ 256`, or an `address`
with no cleanup, as SolidCore's type checker gives a Solidity `address` parameter; each has a
width (`paramWidth`: `b`, or 160 for an address). Its returns are `uint256`, `address` or `bool`
words, and none of its bindings is a storage reference. The tree is the argument checks
(`paramGuards`: a word at or above `2 ^ w` for a parameter of width `w < 256` reverts with empty
data, as SolidCore's decoder, its address check or its `uint b` cleanup, and solar's `lower-abi`
do), then the body's branch tree run from `initState`, with each leaf turned into the call's end
by `leafTree`: the returned words ABI-encoded with the body's storage writes and logs, or a
revert's data (empty, `Panic(code)` or `Error(msg)`) with neither.

Past the argument checks every argument word fits its width, which the facts `argFacts` record
(`gt (arg i) (2 ^ w - 1)` taken as zero). The erasure reads them through the `EraseEnv`'s
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

/-- The width of the argument word of a parameter of the fragment, from its binding and its ABI
cleanup: `b` for a `uint256` with the cleanup `uint b`, `0 < b ≤ 256`, and 160 for an `address` with
no cleanup. -/
def paramWidth (p : BindingDecl) (c : AbiCleanup) : Option Nat :=
  if p.isStorageRef then none
  else
    match p.ty, c with
    | .uint256, .uint b => if 0 < b ∧ b ≤ 256 then some b else none
    | .address, .none => some 160
    | _, _ => none

/-- The widths of the parameters of the fragment, one per parameter and its ABI cleanup. -/
def widthsOf : List BindingDecl → List AbiCleanup → Option (List Nat)
  | [], [] => some []
  | p :: ps, c :: cs => do
    let w ← paramWidth p c
    let ws ← widthsOf ps cs
    some (w :: ws)
  | _, _ => none

/-- The checks of the argument words from parameter `i` on, given their widths: a word of a
parameter of width `w < 256` above `2 ^ w - 1` reverts with empty data. -/
def paramGuards : List Nat → Nat → Tree → Tree
  | [], _, t => t
  | w :: ws, i, t =>
    if w < 256 then
      .ite (.bin .gt (.arg i) (.lit (2 ^ w - 1))) (.halt false [] [] []) (paramGuards ws (i + 1) t)
    else paramGuards ws (i + 1) t

/-- What the argument checks from parameter `i` on leave known: each word of a parameter of
width `w < 256` is at most `2 ^ w - 1`. -/
def argFacts : List Nat → Nat → Facts
  | [], _ => []
  | w :: ws, i =>
    if w < 256 then (.bin .gt (.arg i) (.lit (2 ^ w - 1)), false) :: argFacts ws (i + 1)
    else argFacts ws (i + 1)

/-- The parameters as locals: parameter `i` holds argument word `i`. -/
def paramLocals : List BindingDecl → Nat → Locals
  | [], _ => []
  | p :: ps, i => (p.name, .arg i) :: paramLocals ps (i + 1)

/-- The state a call of `fn` starts in: one scope with its parameters and its returns at zero,
no writes and no logs. -/
def initState (fn : FunctionDef) : SymState :=
  { scopes := [paramLocals fn.params 0 ++ fn.returns.map (fun r => (r.name, .lit 0))]
    writes := []
    logs := [] }

/-- A returned word SolidCore's encoder takes for its type on every call the facts hold on: any
word for a `uint256`, one below `2 ^ 160` for an `address`, at most 1 for a `bool`. -/
def retOk (K : Facts) (ty : Ty) (w : WExpr) : Bool :=
  match ty with
  | .uint256 => true
  | .address => decide (bound K w < 2 ^ 160)
  | .bool => decide (bound K w ≤ 1)
  | _ => false

/-- Every returned word is one SolidCore's encoder takes for its return's type. -/
def retsOk (K : Facts) : List BindingDecl → List WExpr → Bool
  | [], [] => true
  | r :: rs, w :: ws => retOk K r.ty w && retsOk K rs ws
  | _, _ => false

/-- The bytes of SolidCore's `Error(msg)` revert data: the selector `0x08c379a0` and the ABI
encoding of the message, when every byte is one. -/
def errorBytes (msg : String) : Option (List OByte) :=
  match ABI.encodeValues? [.bytesCalldata] [.bytes (ABI.stringBytes msg)] with
  | some p =>
    let bs := ABI.encodeSelector ABI.errorSelector ++ p
    if bs.all (· < 256) then some (bs.map .lit) else none
  | none => none

/-- How a call ends, from how its body ends: the returned words, ABI-encoded, or the named
returns when the body falls through or returns nothing, with the body's writes and logs; a
revert's data, with no writes and no logs. -/
def leafTree (fn : FunctionDef) (K : Facts) : Leaf → Option Tree
  | .normal S => do
    let ws ← fn.returns.mapM fun r => Scopes.get? S.scopes r.name
    if retsOk K fn.returns ws then some (.halt true (ws.flatMap wordOBytes) S.writes S.logs)
    else none
  | .returned S vs =>
    if vs = [] then do
      let ws ← fn.returns.mapM fun r => Scopes.get? S.scopes r.name
      if retsOk K fn.returns ws then some (.halt true (ws.flatMap wordOBytes) S.writes S.logs)
      else none
    else if retsOk K fn.returns vs then
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
  match widthsOf fn.params fn.paramAbiCleanups with
  | none => none
  | some ws =>
    if fn.returns.all wordBinding then do
      let b ← eraseStmt { E with facts := argFacts ws 0 } fuel fn.body (initState fn)
      let t ← brTree fn (argFacts ws 0) b
      some (paramGuards ws 0 t)
    else none

end SolidCore.Refinement.Generic
