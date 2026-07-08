#!/usr/bin/env python3
"""Known-gaps dedup registry + fingerprints (design §6.1b, §6.2).

Every terminal gap gets a ROOT-CAUSE fingerprint (not exact source text) so that
a resubmission of an already-recorded gap is flagged DUPLICATE (no payout to a
second finder of G1). We dedup against TWO registries:

  (i)  the exclusion register (§1) - an OOS hit is not a gap (handled by the
       gate; a submission the gate rejects never reaches dedup); and
  (ii) this known-open-gaps list - the G/H/S/A/C findings pre-loaded with their
       fingerprints so day-one submissions of already-known gaps dedup.

Fingerprint shape (§6.2):
  * lane C: (fail_stage, fail_reason_class, minimal_node_type_or_field)
  * lane S: (observable_component, minimal_feature, delta_shape)

This module is VERSIONED alongside the register. When a gap is FIXED (a Lean fix
lands + a corpus lane pins it), move it to ``KNOWN_FIXED`` so a later resubmission
of the same behavior is NO_DIVERGENCE unless it genuinely regresses.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional


KNOWN_GAPS_VERSION = "1.0.0"


@dataclass(frozen=True)
class GapFingerprint:
    """A root-cause fingerprint. ``key`` is the canonical dedup tuple rendered as
    a stable string; ``lane`` is C or S; ``feature`` is the minimal triggering
    feature."""

    id: str          # G1, H1, S3, A2, C4, ...
    lane: str        # "C" | "S"
    key: tuple       # the §6.2 fingerprint tuple
    feature: str     # human-readable minimal feature
    status: str      # "open" | "fixed"
    note: str = ""

    def key_str(self) -> str:
        return "|".join(str(k) for k in self.key)


# ---------------------------------------------------------------------------
# Pre-loaded known-open gaps. Sources:
#   docs/solidus-solc-deep-comparison.md  (G1-G22)
#   ROADMAP.md "Known semantic gaps (deferred, recorded)"  (H1/H2, S1-S5, etc.)
# The fingerprint keys are deliberately the ROOT CAUSE, matching what the
# adjudicator computes from a live submission (see fingerprint_of_verdict).
# ---------------------------------------------------------------------------

_G_GAPS: list[GapFingerprint] = [
    # --- lane S (soundness / wrong observable / over-accept over-reject) ---
    GapFingerprint("G1", "S",
                   ("return_value", "using-operator-nonbuiltin-body", "wrong-value"),
                   "user-defined operator runs as builtin instead of the operator fn",
                   "open", "CONFIRMED wrong-value"),
    GapFingerprint("G2", "S",
                   ("over_accept", "msg.value-in-view-nonpayable", "over-accept"),
                   "msg.value accepted in view/nonpayable functions", "open"),
    GapFingerprint("G3", "S",
                   ("over_accept", "eq-on-reference-types", "over-accept"),
                   "==/!= accepted on struct/array/bytes/string/mapping", "open"),
    GapFingerprint("G4", "S",
                   ("over_accept", "const-oob-index-bytesN-fixedarray", "over-accept"),
                   "constant out-of-bounds index on bytesN / fixed array", "open"),
    GapFingerprint("G5", "S",
                   ("over_accept", "bare-return-with-named-returns", "over-accept"),
                   "bare `return;` accepted with named returns", "open"),
    GapFingerprint("G6", "S",
                   ("over_accept", "super-to-unimplemented-base", "over-accept"),
                   "super.f() resolves to an unimplemented abstract base fn", "open"),
    GapFingerprint("G7", "S",
                   ("over_accept", "emit-nonevent-member-callee", "over-accept"),
                   "emit A.g() non-event member callee not validated", "open"),
    GapFingerprint("G8", "S",
                   ("over_accept", "revert-shadowing-member", "over-accept"),
                   "revert E(args) with a same-arity shadowing member", "open"),
    GapFingerprint("G9", "S",
                   ("over_accept", "inline-array-literal-of-mapping", "over-accept"),
                   "inline array literal of mapping type [m]", "open"),
    GapFingerprint("G10", "S",
                   ("over_accept", "msg.data-in-receive", "over-accept"),
                   "msg.data in receive() not rejected", "open"),
    GapFingerprint("G11", "S",
                   ("over_accept", "cross-contract-creationcode-cycle", "over-accept"),
                   "cross-contract creationCode/runtimeCode cycle undetected", "open"),
    GapFingerprint("G12", "S",
                   ("over_accept", "identifier-underscore-not-reserved", "over-accept"),
                   "identifier name `_` not reserved", "open"),
    # --- lane C (over-reject: fails closed on a solc-accepted program) ---
    GapFingerprint("G13", "C",
                   ("typecheck", "over_reject", "nested-tuple-LHS"),
                   "nested tuple LHS (((a,),)) = ((1,2),3);", "open"),
    GapFingerprint("G14", "C",
                   ("typecheck", "over_reject", "storage-array-assign-shorter-source"),
                   "storage array assignment with base-convertible/shorter source", "open"),
    GapFingerprint("G15", "C",
                   ("typecheck", "over_reject", "ternary-of-literals-mobile-type"),
                   "ternary-of-literals loses uint8 mobile common type", "open"),
    GapFingerprint("G16", "C",
                   ("typecheck", "over_reject", "try-on-library-usingfor-call"),
                   "try on a library / using-for call over-rejected", "open"),
    # --- G17-G22 untested (probes described; kept as open fingerprints) ---
    GapFingerprint("G17", "S",
                   ("return_value", "storage-ctor-uninit-internal-fn-ptr", "wrong-panic"),
                   "storage/ctor-stored uninitialized internal fn ptr Panic(0x51)", "open"),
    GapFingerprint("G18", "S",
                   ("return_value", "trycatch-multislot-extfnptr-return", "wrong-value"),
                   "try/catch binding of a multi-slot external-fn-ptr return", "open"),
    GapFingerprint("G19", "S",
                   ("over_accept", "mutability-relaxing-override", "over-accept"),
                   "mutability-relaxing overrides (virtual->view/pure)", "open"),
    GapFingerprint("G20", "S",
                   ("over_accept", "using-for-wildcard-imported", "over-accept"),
                   "using ... for * wildcard imported but unexercised", "open"),
    GapFingerprint("G21", "S",
                   ("return_value", "c99-block-scope-self-init", "wrong-value"),
                   "C99 block-scope activation incl. uint x = x; self-init", "open"),
    GapFingerprint("G22", "S",
                   ("return_value", "salted-create-address-prediction", "wrong-value"),
                   "saltedCreate address prediction (OOS-adjacent, needs initcode)",
                   "open", "also covered by SEM-ADDR exclusion"),
]

# H1/H2 (harness) and S1-S5 / A1-A4 / C1-C5 families from the ROADMAP deferred
# registry. Represented at fingerprint granularity so resubmissions dedup even
# though the deep-comparison doc is the canonical G source. These are scaffolds
# for the maintainer to refine as the ROADMAP registry evolves.
_OTHER_GAPS: list[GapFingerprint] = [
    GapFingerprint("H1", "C", ("import", "unimplemented", "harness-H1"),
                   "harness-known gap H1 (see ROADMAP deferred registry)", "open"),
    GapFingerprint("H2", "C", ("import", "unimplemented", "harness-H2"),
                   "harness-known gap H2 (see ROADMAP deferred registry)", "open"),
]


ALL_KNOWN: list[GapFingerprint] = _G_GAPS + _OTHER_GAPS

KNOWN_FIXED: list[GapFingerprint] = []  # populated as fixes land + lanes pin them


def _index() -> dict[str, GapFingerprint]:
    return {g.key_str(): g for g in ALL_KNOWN if g.status == "open"}


def match_fingerprint(lane: str, key: tuple) -> Optional[GapFingerprint]:
    """Return the known-open gap whose fingerprint matches ``key`` exactly, or
    None. The adjudicator computes ``key`` from the live verdict (see
    ``fingerprint_of_verdict``)."""
    fp = "|".join(str(k) for k in key)
    hit = _index().get(fp)
    if hit and hit.lane == lane:
        return hit
    return None


def match_relaxed(lane: str, feature_token: str) -> Optional[GapFingerprint]:
    """A looser dedup by the minimal-feature token (the middle element of the
    fingerprint), used as the maintainer's cluster hint (§6.1d) when the exact
    key differs but the mechanism is the same."""
    for g in ALL_KNOWN:
        if g.status != "open" or g.lane != lane:
            continue
        if len(g.key) >= 2 and g.key[1] == feature_token:
            return g
    return None


def registry_summary() -> dict:
    return {
        "known_gaps_version": KNOWN_GAPS_VERSION,
        "open": [g.id for g in ALL_KNOWN if g.status == "open"],
        "fixed": [g.id for g in KNOWN_FIXED],
    }


if __name__ == "__main__":
    import json
    print(json.dumps(registry_summary(), indent=2))
