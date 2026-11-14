/-
We need a more unified approach to maps.

This file shouldn't exist; but it does for now.
`Finmap`s have terrible computational behaviour, one needs some ordering lemmas to make them compute.

In `Conform`, we use `Lean.RBMap`, although we would ideally use `RBTree.RBMap`, but the `Lean.Json`
uses `Lean.RBMap`, which means that we would need an additional cast to `RBTree.RBMap`.

Furthermore, replacing everything with either of the `RBMaps` would then reintroduce this mess,
but with ordering lemmas needed for some `Decidable` instances.

When time allows, I suggest we replace everything with `RBTree.RBMap` and prove the reasoning lemmas we need.
This way, we get decent performance AND the ability to conveniently reason about the structure
a'la `Finmap`.

TODO - All of this is very ugly.
-/

import Batteries.Data.RBMap

import EvmYul.Wheels

import EvmYul.Maps.StorageMap

import EvmYul.State.Account
import EvmYul.State.AccountOps

namespace EvmYul

section RemoveLater

abbrev AddrMap (α : Type) [Inhabited α] := RBTree.RBMap AccountAddress α compare
abbrev AccountMap (τ : OperationType) := AddrMap (Account τ)
abbrev PersistentAccountMap (τ : OperationType) := AddrMap (PersistentAccountState τ)
def AccountMap.toPersistentAccountMap (τ : OperationType) (a : AccountMap τ) : PersistentAccountMap τ :=
  a.mapVal (λ _ acc ↦ acc.toPersistentAccountState)

def AccountMap.increaseBalance (τ : OperationType) (σ : AccountMap τ) (addr : AccountAddress) (amount : UInt256)
  : AccountMap τ
:=
  match σ.find? addr with
    | none => σ.insert addr {(default : Account τ) with balance := amount}
    | some acc => σ.insert addr {acc with balance := acc.balance + amount}

/--
  Returns `none` in the case of an overflow below zero.
-/
def AccountMap.decreaseBalance (τ : OperationType) (σ : AccountMap τ) (addr : AccountAddress) (amount : UInt256)
  : Option (AccountMap τ)
:=
  match σ.find? addr with
    | none => .none
    | some acc =>
      if acc.balance < amount then .none else .some (σ.insert addr {acc with balance := acc.balance - amount})

/--
  Returns `none` in the case of an overflow below zero.
-/
def AccountMap.transferBalance (τ : OperationType) (σ : AccountMap τ) (from_addr to_addr : AccountAddress) (amount : UInt256)
  : Option (AccountMap τ)
:=
  match (σ.decreaseBalance τ from_addr amount) with
    | .none => .none
    | .some σ' => σ'.increaseBalance τ to_addr amount

def AccountMap.delegatedCodeTarget? (σ : AccountMap .EVM) (t : AccountAddress) :
    Option AccountAddress :=
  match PrecompiledContract.ofAddress? t with
  | some _ => none
  | none =>
      match σ.find? t with
      | none => none
      | some account => account.eip7702DelegationTarget?

def AccountMap.delegatedToExecute (σ : AccountMap .EVM) (t : AccountAddress) :
    ToExecute .EVM :=
  match σ.delegatedCodeTarget? t with
  | none =>
      match σ.find? t with
      | none => ToExecute.Code default
      | some account => ToExecute.Code account.code
  | some target =>
      if (PrecompiledContract.ofAddress? target).isSome then
        ToExecute.Code default
      else
        match σ.find? target with
        | none => ToExecute.Code default
        | some account => ToExecute.Code account.code

def toExecute (τ : OperationType) (σ : AccountMap τ) (t : AccountAddress) : ToExecute τ :=
  match PrecompiledContract.ofAddress? t with
  | some precompiled => ToExecute.Precompiled precompiled
  | none =>
      match τ, σ with
        | .EVM, σ =>
          AccountMap.delegatedToExecute σ t
        | .Yul, σ =>
          match σ.find? t with
          | none => ToExecute.Code default
          | some tDirect => ToExecute.Code tDirect.code

def L_S (σ : PersistentAccountMap .EVM) : Array (ByteArray × ByteArray) :=
  σ.foldl
    (λ arr (addr : AccountAddress) acc ↦
      arr.push (p addr acc)
    )
    .empty
 where
  p (addr : AccountAddress) (acc : PersistentAccountState .EVM) : ByteArray × ByteArray :=
    (ffi.KEC addr.toByteArray, rlp acc)
  rlp (acc : PersistentAccountState .EVM) :=
    Option.get! <|
      RLP <|
        .𝕃
          [ .𝔹 (BE acc.nonce.toNat)
          , .𝔹 (BE acc.balance.toNat)
          , .𝔹 <| (computeTrieRoot acc.storage).getD .empty
          , .𝔹 acc.codeHash.toByteArray
          ]

def stateTrieRoot (σ : PersistentAccountMap .EVM) : Option ByteArray :=
  let a := Array.map toBlobPair (L_S σ)
  (ByteArray.ofBlob (blobComputeTrieRoot a)).toOption
 where
  toBlobPair entry : String × String :=
    let b₁ := EvmYul.toHex entry.1
    let b₂ := EvmYul.toHex entry.2
    (b₁, b₂)

end RemoveLater

end EvmYul
