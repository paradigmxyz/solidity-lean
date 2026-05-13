# SharedSemantics

This top-level folder owns pure semantic foundations for the Solidity source
semantics.

`Word.lean` defines the local `Word` surface while routing EVM-style 256-bit
word operations through the shared `EvmYul.UInt256` primitive surface. The
Nethermind reference checkout lives at `external/nethermind/EVMYulLean`; the
top-level `EvmYul.UInt256` module is the buildable compatibility surface used
until that package can be imported directly under this repo's Lean toolchain.

`External.lean` defines explicit host/external-world records used by the
Solidity source semantics for hashes, account lookups, low-level calls, and
contract creation. These remain source-level oracle boundaries until the source
semantics is connected more deeply to a shared world-state model.
