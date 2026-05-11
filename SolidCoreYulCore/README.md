# SolidCoreYulCore

`SolidCoreYulCore` contains reusable generated-Yul, stack-CFG, bytecode, and EVM
semantics used by the public spine.

The architecture commits only to the generated Yul profile emitted by the
compiler. Broader Yul support files are implementation support for that profile
and for existing proofs; they are not a promise that arbitrary user-written Yul
is part of the verified Solidity-to-EVM claim.
