import EvmYul.Maps.StorageMap
import EvmYul.SpongeHash.Keccak256

import EvmYul.UInt256
import EvmYul.Wheels

import EvmYul.Yul.Ast

namespace EvmYul

inductive PrecompiledContract where
  | ecrec
  | sha256
  | rip160
  | identity
  | expmod
  | bnAdd
  | bnMul
  | snarkv
  | blake2F
  | pointEval
  deriving DecidableEq, Inhabited, Repr

namespace PrecompiledContract

def address : PrecompiledContract → AccountAddress
  | .ecrec => 1
  | .sha256 => 2
  | .rip160 => 3
  | .identity => 4
  | .expmod => 5
  | .bnAdd => 6
  | .bnMul => 7
  | .snarkv => 8
  | .blake2F => 9
  | .pointEval => 10

def all : List PrecompiledContract :=
  [ .ecrec
  , .sha256
  , .rip160
  , .identity
  , .expmod
  , .bnAdd
  , .bnMul
  , .snarkv
  , .blake2F
  , .pointEval
  ]

def ofAddress? (addr : AccountAddress) : Option PrecompiledContract :=
  match addr.val with
  | 1 => some .ecrec
  | 2 => some .sha256
  | 3 => some .rip160
  | 4 => some .identity
  | 5 => some .expmod
  | 6 => some .bnAdd
  | 7 => some .bnMul
  | 8 => some .snarkv
  | 9 => some .blake2F
  | 10 => some .pointEval
  | _ => none

end PrecompiledContract

/--
  Precompiled contract addresses.
  (142) `π ≡ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}`
-/
def π : RBTree.RBSet AccountAddress compare :=
  RBTree.RBSet.ofList (PrecompiledContract.all.map PrecompiledContract.address) compare

inductive ToExecute (τ : OperationType) where
  | Code (code : Yul.Ast.contractCode τ)
  | Precompiled (precompiled : PrecompiledContract)

structure PersistentAccountState (τ : OperationType) where
  nonce    : UInt256
  balance  : UInt256
  storage  : Storage
  code     : (Yul.Ast.contractCode τ)
  codeBytes : ByteArray := default
  deriving BEq, Inhabited, Repr

/--
The `Account` data. Section 4.1.

Suppose `a` is some address.

- `nonce`    -- σ[a]ₙ.
- `balance`  -- σ[a]_b.

In the yellow paper it is supposed to be a 256-bit hash of the root node of
a Merkle Tree. KEVM implemets it as just an key/value map.
- `storage`  -- σ[a]_s.
- `tstorage` -- Transiont storage; added in EIP-1153
- `codeHash` -- σ[a]_c.

For now, we assume no global map `GM` with which `GM[code_hash] ≡ code`.
- `code`
- `codeBytes` -- source-side byte image used by Yul code-image operations
  when this account is entered by a call frame.
-/
structure Account (τ : OperationType) extends PersistentAccountState τ where
  tstorage : Storage
deriving BEq, Inhabited

def PersistentAccountState.codeHash (self : PersistentAccountState .EVM) : UInt256 :=
  .ofNat <| fromByteArrayBigEndian (ffi.KEC self.code)

def Account.codeHash (self : (Account .EVM)) : UInt256 :=
  self.toPersistentAccountState.codeHash

def eip7702DelegationTargetOfCode? (code : ByteArray) : Option AccountAddress :=
  if code.size == 23
      && code.get? 0 == some 0xef
      && code.get? 1 == some 0x01
      && code.get? 2 == some 0x00 then
    some <| .ofNat <| fromByteArrayBigEndian (code.readWithoutPadding 3 20)
  else
    none

def Account.eip7702DelegationTarget? (self : Account .EVM) : Option AccountAddress :=
  eip7702DelegationTargetOfCode? self.code

end EvmYul
