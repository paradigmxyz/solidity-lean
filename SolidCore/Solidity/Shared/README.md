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

`Account.lean` owns account-facing wrappers such as address normalization and
balance/code/codehash lookup.

`Call.lean` owns low-level call and contract-creation request/result surfaces,
including the EVM-shaped call/create oracle boundary. Call requests include the
optional source-specified gas value so Solidity `{gas: ...}` options and
`send`/`transfer` stipends are visible to every layer that uses the shared call
surface.

`Log.lean` owns the shared log append surface used by Solidity event emission
while Solidity keeps source-level event declaration and ABI encoding rules.

`Precompile.lean` owns address-keyed precompile calls for source-level
`ecrecover`, `sha256`, and `ripemd160`, reusing the shared low-level call
result surface at addresses `0x01`, `0x02`, and `0x03`.

`External.lean` is a compatibility/helper surface for byte normalization and
older external-world records that have not yet been retired. New shared
operation surfaces should live in named modules such as `Account`, `Block`,
`Call`, `Log`, or `Precompile`.
