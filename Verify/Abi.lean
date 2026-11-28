import Verify.Basic
import SolidCore.Refinement.Wide.Refines

/-!
# Argument words of a call

A specification speaks about a call's argument words. `argWords n call` reads the
first `n` of them from the call data after the selector, as SolidCore's ABI decoder
does; on a call of `Abi.fullScope` they are the words the call was built from
(`argWords_calldata`).
-/

namespace SolidCore.Verify

open SolidCore.Refinement SolidCore.Solidity SolidCore.Solidity.Source

/-- The first `n` argument words of `call`: the 32-byte words after the selector. -/
def argWords (n : Nat) (call : Call) : List Nat :=
  (List.range n).map fun i =>
    (ABI.readWord? ((call.calldata.data.toList.map (·.toNat)).drop 4) (32 * i)).getD 0

theorem argWords_calldata (sel : Nat) (args : List Nat) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (cv : Nat) (st : List (Nat × Nat)) :
    argWords args.length { calldata := Abi.calldata sel args, callvalue := cv, storage := st } =
      args := by
  simp only [argWords, Dirty.bytes_calldata, Wide.drop_selector]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [Dirty.readWord_argBytes args hargs i h2]

/-- The bytes of a 32-byte big-endian word. -/
def word (v : Nat) : List Nat := (EthLib.Base.natToBytes 32 v).map (·.toNat)

/-- The revert data of `Panic(code)`. -/
def panic (code : Nat) : List Nat := (EthLib.Base.natToBytes 4 0x4e487b71).map (·.toNat) ++ word code

end SolidCore.Verify

