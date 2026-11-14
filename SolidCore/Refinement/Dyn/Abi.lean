import SolidCore.Refinement.Evm.Calldata

/-!
# Calls with dynamic ABI parameters and malformed call data

`Abi.lean` describes a call as its selector followed by one clean word per
parameter. A function with dynamic parameters (`bytes calldata`, `T[] calldata`)
or a static struct takes call data of any length, so this module describes a call
as its selector followed by any bytes, and splits the call data a function can be
given into two scopes:

* `encodings`: the canonical ABI encoding of every argument tuple up to a bound:
  every byte string of length at most `n` for `bytes`, every array of clean words
  of length at most `n` for `T[]`, every tuple of clean words for a struct. Each
  dynamic argument's tail follows the heads in order, at the offset its head
  word names. These calls are finitely many and a proof checks them by evaluation.
* `Malformed`: call data no ABI decoder accepts: shorter than the heads, or with a
  dynamic argument whose offset word points past the end of the call data, or
  whose length word runs its tail past the end. Every such call data, of any
  length below `2 ^ 32` and with any bytes, is in scope; a proof shows both
  semantics revert on it with empty output, symbolically.

Call data that the decoders accept but that is not a canonical encoding within
the bound (another offset, trailing bytes, nonzero padding, a longer tail, dirty
words) is in neither scope.

Words are read as CALLDATALOAD reads them, `wordAt`: 32 bytes big-endian, zero
past the end.
-/

namespace SolidCore.Refinement.Dyn

open EthLib.Base EthLib.Execution.Evm SolidCore.Refinement.Abi

/-- A parameter of a function, static or dynamic, with the bound of its encodings. -/
inductive DParam where
  /-- A word of a static ABI type. -/
  | word (p : Param)
  /-- `bytes calldata`, encoded up to `bound` bytes. -/
  | bytes (bound : Nat)
  /-- `T[] calldata` of a static word type `p`, encoded up to `bound` elements. -/
  | array (p : Param) (bound : Nat)
  /-- A struct of static words, in the head. -/
  | struct (ps : List Param)
  deriving Repr, DecidableEq

/-- The words a parameter takes in the head. -/
def DParam.headWords : DParam → Nat
  | .struct ps => ps.length
  | _ => 1

/-- The bytes per element of a dynamic parameter's tail, or none for a static one. -/
def DParam.stride? : DParam → Option Nat
  | .bytes _ => some 1
  | .array _ _ => some 32
  | _ => none

/-- The words the parameters take in the head. -/
def headWords : List DParam → Nat
  | [] => 0
  | p :: ps => p.headWords + headWords ps

/-- The word at byte `p` of `data`, as CALLDATALOAD reads it: 32 bytes big-endian, zero
past the end. -/
def wordAt (data : ByteArray) (p : Nat) : Nat := (loadWord data p 32).toNat

/-- Whether the dynamic argument whose head word is at byte `pos` points past the end of
`data`: its offset leaves no room for its length word, or its length runs its tail of
`stride`-byte elements past the end. -/
def TailPastEnd (data : ByteArray) (pos stride : Nat) : Prop :=
  data.size < wordAt data pos + 32 ∨
    data.size < wordAt data pos + 32 + wordAt data (wordAt data pos) * stride

/-- The byte position of the head word and the element stride of each dynamic parameter,
for parameters whose heads start at byte `pos`. -/
def dynHeads : List DParam → Nat → List (Nat × Nat)
  | [], _ => []
  | p :: ps, pos =>
    (match p.stride? with
      | some k => [(pos, k)]
      | none => []) ++ dynHeads ps (pos + 32 * p.headWords)

/-- Call data, after the selector, that no ABI decoder of `ps` accepts: shorter than the
heads, or with a dynamic argument that points past the end. -/
def Malformed (ps : List DParam) (data : ByteArray) : Prop :=
  data.size < 32 * headWords ps ∨ ∃ e ∈ dynHeads ps 0, TailPastEnd data e.1 e.2

/-! ## Canonical encodings -/

/-- Every list of length at most `n` of elements of `xs`, shortest first. -/
def upTo {α : Type} (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: xs.flatMap fun x => (upTo xs n).map (x :: ·)

/-- The 32 big-endian bytes of a word. -/
def word32 (v : Nat) : List UInt8 := natToBytes 32 v

/-- An argument's encoding: its head bytes for a static one, its tail for a dynamic one. -/
structure Piece where
  /-- Whether the bytes are a tail that the head points to. -/
  tail : Bool
  /-- The bytes. -/
  bytes : List UInt8

/-- Every encoding of the parameter within its bound. -/
def DParam.pieces : DParam → List Piece
  | .word p => p.values.map fun v => ⟨false, word32 v⟩
  | .struct ps => (tuples ps).map fun vs => ⟨false, vs.flatMap word32⟩
  | .bytes n => (upTo ((List.range 256).map Nat.toUInt8) n).map fun bs =>
      ⟨true, word32 bs.length ++ bs ++ List.replicate ((32 - bs.length % 32) % 32) 0⟩
  | .array p n => (upTo p.values n).map fun vs =>
      ⟨true, word32 vs.length ++ vs.flatMap word32⟩

/-- The heads of the arguments, with each tail's offset counted from `off`, and the tails. -/
def assemble : List Piece → Nat → List UInt8 × List UInt8
  | [], _ => ([], [])
  | p :: ps, off =>
    if p.tail then
      let r := assemble ps (off + p.bytes.length)
      (word32 off ++ r.1, p.bytes ++ r.2)
    else
      let r := assemble ps off
      (p.bytes ++ r.1, r.2)

/-- The ABI encoding of the arguments: the heads, then the tails in order. -/
def encode (ps : List DParam) (pieces : List Piece) : ByteArray :=
  let r := assemble pieces (32 * headWords ps)
  ⟨(r.1 ++ r.2).toArray⟩

/-- Every list of one encoding per parameter. -/
def pieceTuples : List DParam → List (List Piece)
  | [] => [[]]
  | p :: ps => p.pieces.flatMap fun x => (pieceTuples ps).map (x :: ·)

/-- A function of a contract: its selector and its parameters. -/
structure DFn where
  /-- The function's selector. -/
  sel : Nat
  /-- Its parameters, in order. -/
  params : List DParam

/-- The call of the function with selector `sel` on the call data `data` after the
selector, with no value, from storage `s`. -/
def callOn (sel : Nat) (data : ByteArray) (s : List (Nat × Nat)) : Call :=
  { calldata := Evm.selectorOf sel ++ data, callvalue := 0, storage := s }

/-- Every call of a function of `fns` on the canonical encoding of an argument tuple within
the bounds, from each storage of `storages`. -/
def encodings (fns : List DFn) (storages : List (List (Nat × Nat))) : List Call :=
  storages.flatMap fun s => fns.flatMap fun fn =>
    (pieceTuples fn.params).map fun pcs => callOn fn.sel (encode fn.params pcs) s

/-- Every call of a function of `fns` from storage `s` with no value whose call data is a
canonical encoding within the bounds, or the selector followed by any malformed bytes
shorter than `2 ^ 32`. -/
def dynScope (fns : List DFn) (s : List (Nat × Nat)) (call : Call) : Prop :=
  call ∈ encodings fns [s] ∨
    ∃ fn ∈ fns, ∃ data : ByteArray, data.size < 2 ^ 32 ∧ Malformed fn.params data ∧
      call = callOn fn.sel data s

end SolidCore.Refinement.Dyn
