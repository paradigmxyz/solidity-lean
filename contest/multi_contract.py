#!/usr/bin/env python3
"""v2 SEAM: multi-contract closed-world reflective execution (design §3, §8).

THIS IS A STUB. v1 ships single-contract only (design §3.3, §8): the reject gate
enforces the temporary ``V1-MULTI`` guard (see reject_gate.detect_v1_multi), so
submissions with >1 concrete deployable contract are rejected until v2.

The v1 code path (harness_bridge.run_solidity_lean_observable) uses the existing
RESPONDER-FREE interpreter entry point (``CheckedInput.ownCall``). That entry
point is the single-contract case of the general closed-world run; everything
below documents exactly where the multi-contract responder plugs in so the v2
build is wiring, not redesign.

------------------------------------------------------------------------------
WHERE v2 PLUGS IN (all reuse of existing, proved Lean machinery - §3.2):

1. Contract registry builder (design item #9):
   Build a `Word -> Contract` map from the Forge test's DEPLOY ORDER (each
   `new C()` in the test gets a nonce-derived CREATE address matching Foundry's
   `keccak(rlp(sender, nonce))[12:]`; keep create2 *address* OOS per SEM-ADDR).
   -> implement ``build_registry(submission) -> RegistrySpec`` here.

2. Reflective responder (design item #7):
   A Lean answerer ``reflectiveResponder registry depth`` mirroring
   `ScriptedResponder.answerCall?` / `answerCreate?` (Interpreter.lean:2601/2641)
   but INVOKING the interpreter on the submitted callee via
   `Contract.callCalldataAtFromWithContext?` (ABI.lean:676) and encoding the
   `AbiCallResult` + `snapshotWorld` back into a `CallResponse` / `CreateResponse`.
   The proved round-trip law `snapshotWorld (adoptWorld w ...) = w`
   (AdoptionLaws.lean) makes closed-world composition sound by the SAME law that
   makes reentrancy adoption sound.
   -> emitted as an extra Lean def alongside observable.LEAN_OBSERVABLE_HELPER.

3. Depth-bounded fold (design item #8 - the ONE genuine new recursion obligation):
   A call-depth `Nat` decreasing per nested external call; exhaustion => a
   well-defined failure mirroring EVM's 1024 call-depth limit (itself a
   checkable observable, since solc+EVM also revert at depth 1024).
   -> ``DEFAULT_CALL_DEPTH = 1024`` below is the intended bound.

4. Multi-contract observable extractor (design item #10):
   events + observed storage across the closed-world subcall tree, not just the
   top return value. observable.Observable already reserves fields 4 (events)
   and 5 (state) for this; the v1 comparator checks outcome/return/revert/panic
   (§3.4 items 1-3), which cover every G1-G22 value/revert divergence.

5. Retire V1-MULTI (design item #11): pass ``enforce_v1_multi=False`` to the gate.
------------------------------------------------------------------------------
"""

from __future__ import annotations

from dataclasses import dataclass, field


DEFAULT_CALL_DEPTH = 1024  # mirrors EVM's call-depth limit (§3.2)


@dataclass
class RegistrySpec:
    """v2: deploy-address -> contract-name map, from the Forge deploy order."""

    deploy_order: list[str] = field(default_factory=list)
    address_by_name: dict[str, str] = field(default_factory=dict)


def build_registry(*_args, **_kwargs) -> RegistrySpec:  # pragma: no cover - v2 stub
    raise NotImplementedError(
        "multi-contract reflective execution is a v2 feature (design §3/§8). "
        "v1 rejects multi-contract submissions via the V1-MULTI gate guard.")
