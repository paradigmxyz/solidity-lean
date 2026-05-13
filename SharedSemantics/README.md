# SharedSemantics

This top-level folder owns pure semantic foundations for the Solidity source
semantics.

`Word.lean` defines the local `Word` surface while routing EVM-style 256-bit
word operations through the shared `EvmYul.UInt256` primitive surface. The
Nethermind reference checkout lives at `external/nethermind/EVMYulLean`; the
top-level `EvmYul.UInt256` module is the buildable compatibility surface used
until that package can be imported directly under this repo's Lean toolchain.

`EvmYul/SpongeHash/Keccak256.lean` is the matching buildable Keccak primitive
surface used by Solidity ABI/event selectors and source-level `keccak256`.

`Block.lean` owns ambient block and transaction context primitives shared by
source Solidity and future Yul/EVM adapters: block fields, transaction fields,
`blockhash`, and `blobhash`. Solidity keeps its own storage and memory model.

`Account.lean` owns account-facing wrappers such as address normalization,
balance/code/codehash lookup, and `ecrecover` oracle tables.

`Call.lean` owns low-level call and contract-creation request/result surfaces,
including the EVM-shaped call/create oracle boundary.

`Log.lean` owns the shared log append surface used by Solidity event emission
while Solidity keeps source-level event declaration and ABI encoding rules.

`External.lean` defines explicit host/external-world records used by the
Solidity source semantics for hashes, account lookups, low-level calls, and
contract creation. These remain source-level oracle boundaries until the source
semantics is connected more deeply to a shared world-state model.
