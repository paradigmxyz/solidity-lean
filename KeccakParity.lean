import EvmYul.FFI.ffi
import SolidCore.Solidity.Keccak

/-!
Byte-parity witness: the pure Keccak-256 (`SolidCore.Solidity.Source.Keccak`,
since pin `b08573c` a re-export of `EvmYul.SpongeHash.Keccak256` — the same
definition that is now the Lean body of `ffi.keccak256`) vs the NATIVE
`keccak256` extern symbol the compiled path actually executes. Logically the
two sides are the same function; this witness checks the native code agrees
with the Lean body byte-for-byte.

The pinned hash is native-only, so it cannot be evaluated from the total
interpreter or the harness `#eval` path; this executable links the pinned
`libleanffi` static library (via `supportInterpreter := true`) so the two
implementations can be compared directly on concrete inputs. Run with
`lake exe keccakParity`; it exits 0 iff every case agrees byte-for-byte.
-/

open SolidCore.Solidity.Source

private def pureKec (bytes : List Nat) : List Nat :=
  Keccak.keccak256Bytes bytes

private def ffiKec (bytes : List Nat) : List Nat :=
  (ffi.KEC (ByteArray.mk (Array.mk (bytes.map (fun n => UInt8.ofNat n))))).toList.map UInt8.toNat

/-- Representative inputs: empty, real ABI selectors/signatures the corpus relies
on, event-topic-shaped strings, and multi-block byte ranges crossing the 136-byte
rate boundary. -/
private def parityCases : List (List Nat) :=
  [ [],
    Keccak.bytesOfString "transfer(address,uint256)",
    Keccak.bytesOfString "balanceOf(address)",
    Keccak.bytesOfString "Transfer(address,address,uint256)",
    Keccak.bytesOfString "Approval(address,address,uint256)",
    Keccak.bytesOfString "approve(address,uint256)",
    List.range 32,
    List.range 135,
    List.range 136,
    List.range 137,
    List.range 300 ]

def keccakParityHolds : Bool :=
  parityCases.all (fun c => pureKec c == ffiKec c)

def main : IO UInt32 := do
  if keccakParityHolds then
    IO.println s!"keccak parity: OK ({parityCases.length} cases, pure == pinned FFI)"
    return 0
  else
    IO.eprintln "keccak parity: MISMATCH between pure Keccak and pinned FFI"
    return 1
