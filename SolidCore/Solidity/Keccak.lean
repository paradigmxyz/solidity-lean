import EvmYul.SpongeHash.Keccak256

/-!
Keccak-256, re-exported from the pinned EVMYulLean package.

Since evmyul pin `b08573c` the package provides the pure, total Keccak-256
sponge (`EvmYul.SpongeHash.Keccak256`) as the *logical meaning* of the native
`keccak256` symbol (`ffi.keccak256` is a `def` whose body is that sponge, with
`@[extern]` acceleration). The former repo-owned implementation — itself the
verbatim ancestor of the package's — is deleted; this module keeps the
historical `SolidCore.Solidity.Source.Keccak.*` names as aliases so the
interpreter, elaboration, witnesses, and harness are unchanged.

Consequence: this repo's keccak and the EVM/Yul target semantics' keccak are
now the *same definition*, so future lowering seams need no keccak-equality
hypothesis. Byte-parity of the pure body against the native symbol is still
witnessed by `lake exe keccakParity`.
-/

namespace SolidCore
namespace Solidity
namespace Source
namespace Keccak

abbrev Byte := Nat

abbrev keccak256Bytes : List Byte → List Byte :=
  EvmYul.SpongeHash.Keccak256.keccak256Bytes

abbrev bytesOfString : String → List Byte :=
  EvmYul.SpongeHash.Keccak256.bytesOfString

abbrev keccak256String : String → List Byte :=
  EvmYul.SpongeHash.Keccak256.keccak256String

abbrev wordFromBytesBE : List Byte → Nat :=
  EvmYul.SpongeHash.Keccak256.wordFromBytesBE

abbrev selector4 : String → Nat :=
  EvmYul.SpongeHash.Keccak256.selector4

abbrev digestWord : String → Nat :=
  EvmYul.SpongeHash.Keccak256.digestWord

end Keccak
end Source
end Solidity
end SolidCore
