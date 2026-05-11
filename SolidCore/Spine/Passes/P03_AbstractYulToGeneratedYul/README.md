# P03 AbstractYul To GeneratedYul

This pass concretizes abstract effects into the generated Yul profile: ABI,
storage layout, event/error encoding, memory discipline, and emitted helpers.

The authoritative interface is `Interface.lean`; architectural intent lives in
`ARCHITECTURE.md`.
