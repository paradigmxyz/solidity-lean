#!/usr/bin/env python3
"""Known-gaps dedup registry + fingerprints (design §6.1b, §6.2).

Every terminal gap gets a ROOT-CAUSE fingerprint (not exact source text) so that
a resubmission of an already-recorded gap is flagged DUPLICATE (no leaderboard
credit to a second finder of G1). We dedup against TWO registries:

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


KNOWN_GAPS_VERSION = "1.3.0"  # release audit: H1/H2 dead scaffold removed;
#                               KNOWN_FIXED reconciled against DIVERGENCE-LOG.md
#                               (DL52..DL205 provenance entries added).
# v1.2: +rounds 2-12 open gaps (CF3/CS1 open, CB1 extcall);
#       +E1/E2/O1/CF2/PT1/CL1/PK1/UF1-3/V1/A1-interfaceId fixed


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
#   docs/solidity-lean-solc-deep-comparison.md  (G1-G22)
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

# H1/H2 removed (release audit): they were placeholder scaffold rows whose keys
# ("import", "unimplemented", "harness-H1"/"harness-H2") could NEVER match a live
# adjudicator fingerprint — the lane-C import fingerprint's third element is the
# sorted node/field token set from the importer fail message (_first_token), so
# the literal string "harness-H1" is unproducible. Dead rows in the open index
# are worse than absent rows: they inflate the "known open" list and imply dedup
# coverage that does not exist. If concrete ROADMAP-deferred harness gaps are
# ever fingerprintable, add them with keys in the REAL fingerprint format.

# Round 2-12 implementation-divergence review findings (docs/solc-implementation-
# divergences{,-2..-10}.md) that are OPEN and confirmed-or-inferred but NOT already
# a G/H/A entry above. Each is fingerprinted at root-cause granularity so a public
# submission of the known behavior dedups. Intentional exclusions (inline-assembly
# CF1, create2 address G22) and non-divergences (AE1, AD1, N1/N2, T2-T5, all F*/N*
# "faithful" rows) are deliberately NOT listed — they never reach dedup.
_ROUND_GAPS: list[GapFingerprint] = [
    # --- lane C (over-reject: fails closed on a solc-accepted program) ---
    GapFingerprint("CF3", "C",
                   ("typecheck", "over_reject", "ctrlflow-fuel-placeholder-fallback"),
                   "control-flow pointer-return analysis falls back to unsafeReturn on "
                   "fuel exhaustion / bare modifier-placeholder (over-rejects deep bodies)",
                   "open", "round 2 §3c; INFERRED, effectively unreachable; verify open/fixed"),
    # --- lane S (soundness: solidity-lean runs but the observable differs) ---
    GapFingerprint("CS1", "S",
                   ("return_value", "selfdestruct-balance-transfer", "wrong-value"),
                   "selfdestruct records (from,recipient,deletesAccount) but does NOT "
                   "move the balance (self not zeroed, recipient not credited)",
                   "open", "round 11 (doc -9); CONFIRMED-by-trace, reachability UNTESTED "
                   "(live iff post-destruct balances are compared); verify open/fixed"),
]

# External-call / try-catch divergences confirmed in the semantics review
# (docs/semantics-divergence-handoff.md, A1-A3). These are currently OUT OF SCOPE
# in v1 via the X-EXTCALL exclusion (external calls are unmodeled), so a live v1
# submission never reaches dedup; they are recorded here so they dedup once the
# v2 reflective responder lands and X-EXTCALL is retired.
_EXTCALL_GAPS: list[GapFingerprint] = [
    GapFingerprint("A1", "S",
                   ("revert_data", "try-void-call-codeless-address", "revert-vs-success"),
                   "try over a void external call to a codeless/EOA address: "
                   "solidity-lean runs catch, solc reverts the caller uncatchably",
                   "open", "OOS via X-EXTCALL in v1; live for v2"),
    GapFingerprint("A2", "S",
                   ("return_value", "catch-clause-source-order-vs-kind", "wrong-value"),
                   "catch-clause dispatch is source-order first-match; solc "
                   "dispatches by kind (fallback catch listed first shadows Error/Panic)",
                   "open", "OOS via X-EXTCALL in v1; live for v2"),
    GapFingerprint("A3", "S",
                   ("revert_data", "extcodesize-nonident-receiver", "revert-vs-success"),
                   "extcodesize existence check skipped for non-identifier receiver "
                   "shapes (arr[i].f(), s.field.f(), m[k].f()) on a plain void call",
                   "open", "OOS via X-EXTCALL in v1; live for v2"),
    GapFingerprint("CB1", "S",
                   ("return_value", "trycatch-short-error-clause-dispatch", "wrong-value"),
                   "try/catch Error(string) clause matches a short (<0x44 B) non-canonical "
                   "Error-selector payload solc routes to catch(bytes): solidity-lean's strict "
                   "codec lacks solc's returndatasize()>=0x44 gate -> wrong branch + value",
                   "open", "round 9 (doc -8); OOS via X-EXTCALL in v1; live for v2"),
]


ALL_KNOWN: list[GapFingerprint] = _G_GAPS + _ROUND_GAPS + _EXTCALL_GAPS

# Gaps FIXED on this branch (a Lean fix + corpus lane landed). A resubmission of
# one of these is NO_DIVERGENCE unless it genuinely regresses. Recorded (not
# matched against the open index) for provenance. Fingerprints are best-effort.
KNOWN_FIXED: list[GapFingerprint] = [
    GapFingerprint("DL1", "S",
                   ("return_value", "storage-ctor-initializer-order", "wrong-value"),
                   "storage/constructor/initializer evaluation order = reverse-C3",
                   "fixed", "fix commit 4d2a5c0"),
    GapFingerprint("M1", "S",
                   ("return_value", "memory-alias-reference-assignment", "wrong-value"),
                   "memory reference-type assignment aliased (not deep-copied)",
                   "fixed", "fix commit ce58cfd (M1/M2/M3)"),
    GapFingerprint("M4", "S",
                   ("return_value", "memory-deep-deref-encode-keccak", "wrong-value"),
                   "abi.encode/keccak of ref-nested memory deep-deref",
                   "fixed", "fix commit 3043a9b (M4)"),
    # Round 2-6 acceptance-boundary + wrong-value findings, each with a landed fix.
    GapFingerprint("E1", "S",
                   ("over_accept", "nonrational-immutable-read-in-pure", "over-accept"),
                   "pure fn reading a non-rational-initialized immutable (keccak/abi/"
                   "constant-ref) accepted; solc errors 2527 (View)",
                   "fixed", "fix commit ce810e1 (rational-only immutable pure-read)"),
    GapFingerprint("E2", "C",
                   ("typecheck", "over_reject", "this-f-selector-in-pure"),
                   "this.f.selector in a pure/non-view function over-rejected",
                   "fixed", "fix commit 3c86aad"),
    GapFingerprint("O1", "S",
                   ("over_accept", "duplicate-contract-in-override-list", "over-accept"),
                   "override(A, A) duplicate contract in the override list accepted; "
                   "solc errors 4520",
                   "fixed", "fix commit beba717"),
    GapFingerprint("CF2", "C",
                   ("typecheck", "over_reject", "no-revert-pruning-always-reverting-callee"),
                   "pointer-return analysis lacked revert-pruning of always-reverting "
                   "callees (over-reject); solc prunes via ControlFlowRevertPruner",
                   "fixed", "fix commit 51959a7 (always-reverts fixpoint)"),
    GapFingerprint("PT1", "S",
                   ("over_accept", "constant-cyclic-dependency", "over-accept"),
                   "self/mutually-cyclic `constant` accepted; solc errors 6161",
                   "fixed", "fix commit ce810e1 (constantsHaveCycle)"),
    GapFingerprint("CL1", "S",
                   ("over_accept", "bare-modifier-base-ctor-zeroparam", "over-accept"),
                   "bare modifier-style base-constructor call on a zero-param base "
                   "accepted; solc errors 1563",
                   "fixed", "fix commit 5cd1903 (hasArgList flag)"),
    GapFingerprint("PK1", "C",
                   ("typecheck", "over_reject", "encodepacked-nested-static-array"),
                   "abi.encodePacked of a nested static value-array (uint[2][3]) "
                   "over-rejected; solc encodes it",
                   "fixed", "fix commit 5cd1903 (nested-static-array encodePacked)"),
    GapFingerprint("UF1", "C",
                   ("typecheck", "over_reject", "using-for-global-nonudvt"),
                   "using L/{f} for T global; on a struct/enum (non-UDVT user type) "
                   "over-rejected; solc accepts",
                   "fixed", "fix commit 9cd70d3 (using-for global directive legality)"),
    GapFingerprint("UF2", "S",
                   ("over_accept", "operator-binding-mixed-params", "over-accept"),
                   "operator binding whose fn params are not both the target type "
                   "accepted at decl; solc errors 1884",
                   "fixed", "fix commit 9cd70d3"),
    GapFingerprint("UF3", "S",
                   ("over_accept", "duplicate-operator-binding", "over-accept"),
                   "duplicate operator binding for the same operator+type (never used) "
                   "accepted; solc errors 4705",
                   "fixed", "fix commit 9cd70d3"),
    GapFingerprint("V1", "S",
                   ("revert_data", "calldata-slice-oob-revert-data", "wrong-revert"),
                   "calldata-slice OOB (a[i:j]) reverted Panic(0x32) instead of solc's "
                   "empty revert(0,0)",
                   "fixed", "fix commit db26356"),
    GapFingerprint("A1IF", "C",
                   ("elaboration", "elab_reject", "abstract-contract-interfaceId-lowering"),
                   "type(AbstractContract).interfaceId failed to lower (interface-only "
                   "interfaceIdEnv) -> wrong-reject; solc computes it",
                   "fixed", "fix commit 3ed95f1 (round 6 A1; distinct from extcall A1)"),
]

# ---------------------------------------------------------------------------
# DIVERGENCE-LOG.md reconciliation (release audit): every log row whose fix has
# LANDED ON MAIN (status merged / RESOLVED BY REARCH / CLOSED BY REARCH),
# recorded here as PROVENANCE so an already-fixed divergence is traceable if a
# resubmission of it ever surfaces (a resubmission normally adjudicates
# NO_DIVERGENCE — the engine no longer diverges — unless it genuinely
# regresses, in which case this list tells the maintainer it is a regression,
# not a novel find). Ids are DL<row#> (DL<row#>b for a duplicated row number).
# Keys are BEST-EFFORT §6.2-shaped (feature slug = the log row's headline
# name); like the rest of KNOWN_FIXED they are provenance-grade only and are
# NEVER matched against the open dedup index. Non-fixed rows (found/queued/
# built-not-merged/HELD/BACKLOG), verified-correct rows, and the proved-
# unreachable #153 are intentionally absent — they are not landed fixes.
# Generated from DIVERGENCE-LOG.md (2026-07-20); regenerate on log changes.
_DIVERGENCE_LOG_FIXED: list[GapFingerprint] = [
    GapFingerprint("DL52", "C",
                   ("typecheck", "over_reject", "ec-cmp"),
                   "ec-cmp",
                   "fixed", "log #52; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL53", "S",
                   ("return_value", "fp-eq-2", "wrong-value"),
                   "fp-eq-2",
                   "fixed", "log #53; wrong-value; merged (see log row for commit)"),
    GapFingerprint("DL54", "S",
                   ("over_accept", "mod-ret", "over-accept"),
                   "mod-ret",
                   "fixed", "log #54; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL55", "C",
                   ("typecheck", "over_reject", "base-call"),
                   "base-call",
                   "fixed", "log #55; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL56", "S",
                   ("over_accept", "al1", "over-accept"),
                   "al1",
                   "fixed", "log #56; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL57", "C",
                   ("typecheck", "over_reject", "tup-idx"),
                   "tup-idx",
                   "fixed", "log #57; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL58", "C",
                   ("typecheck", "over_reject", "al-exec"),
                   "al-exec",
                   "fixed", "log #58; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL59", "S",
                   ("return_value", "uni1", "wrong-value"),
                   "uni1",
                   "fixed", "log #59; wrong-value; merged (see log row for commit)"),
    GapFingerprint("DL62", "S",
                   ("return_value", "dec-oom", "wrong-value"),
                   "dec-oom",
                   "fixed", "log #62; wrong-value; merged (see log row for commit)"),
    GapFingerprint("DL63", "S",
                   ("over_accept", "get-struct", "over-accept"),
                   "get-struct",
                   "fixed", "log #63; over-accept + wrong-sig; merged (see log row for commit)"),
    GapFingerprint("DL69", "S",
                   ("over_accept", "priv-shadow", "over-accept"),
                   "priv-shadow",
                   "fixed", "log #69; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL70", "C",
                   ("typecheck", "over_reject", "callpos-family"),
                   "callpos-family",
                   "fixed", "log #70; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL70b", "C",
                   ("typecheck", "over_reject", "call-position"),
                   "call-position",
                   "fixed", "log #70; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL73", "C",
                   ("typecheck", "over_reject", "extcall-binary"),
                   "extcall-binary",
                   "fixed", "log #73; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL74", "C",
                   ("typecheck", "over_reject", "emit-qual"),
                   "emit-qual",
                   "fixed", "log #74; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL77", "C",
                   ("typecheck", "over_reject", "revert-qual"),
                   "revert-qual",
                   "fixed", "log #77; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL78", "S",
                   ("over_accept", "encpacked-lit", "over-accept"),
                   "encpacked-lit",
                   "fixed", "log #78; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL80", "C",
                   ("typecheck", "over_reject", "sb-a"),
                   "sb-a",
                   "fixed", "log #80; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL81", "S",
                   ("over_accept", "div-dup-inh-mod", "over-accept"),
                   "div-dup-inh-mod",
                   "fixed", "log #81; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL82", "S",
                   ("over_accept", "usingfor-brace", "over-accept"),
                   "usingfor-brace",
                   "fixed", "log #82; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL83", "S",
                   ("return_value", "d-oom-dispatch", "wrong-value"),
                   "d-oom-dispatch",
                   "fixed", "log #83; wrong-value; merged (see log row for commit)"),
    GapFingerprint("DL84", "S",
                   ("return_value", "tc-oom1", "wrong-value"),
                   "tc-oom1",
                   "fixed", "log #84; wrong-value; merged (see log row for commit)"),
    GapFingerprint("DL86", "S",
                   ("over_accept", "cmp-mixedsign", "over-accept"),
                   "cmp-mixedsign",
                   "fixed", "log #86; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL93", "C",
                   ("typecheck", "over_reject", "lib-storage-public-2"),
                   "lib-storage-public-2",
                   "fixed", "log #93; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL94", "S",
                   ("over_accept", "str-overaccept---payable-vis", "over-accept"),
                   "str-overaccept / payable-vis",
                   "fixed", "log #94; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL95", "C",
                   ("typecheck", "over_reject", "push-field-lvalue"),
                   "push-field-lvalue",
                   "fixed", "log #95; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL101", "C",
                   ("typecheck", "over_reject", "calldata-lazy-value"),
                   "calldata-lazy-value",
                   "fixed", "log #101; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL102", "C",
                   ("typecheck", "over_reject", "qualified-member-cluster"),
                   "qualified-member cluster",
                   "fixed", "log #102; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL104", "S",
                   ("over_accept", "syntax-overaccept", "over-accept"),
                   "syntax-overaccept",
                   "fixed", "log #104; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL105", "S",
                   ("over_accept", "dup-event-sibling", "over-accept"),
                   "dup-event-sibling",
                   "fixed", "log #105; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL106", "S",
                   ("over_accept", "inherited-identifier-clash", "over-accept"),
                   "inherited-identifier-clash",
                   "fixed", "log #106; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL108", "S",
                   ("return_value", "abi-decode-address-payable", "wrong-value"),
                   "abi-decode-address-payable",
                   "fixed", "log #108; wrong-value; merged (see log row for commit)"),
    GapFingerprint("DL109", "C",
                   ("typecheck", "over_reject", "common-type-literal-mobile"),
                   "common-type-literal-mobile",
                   "fixed", "log #109; wrong-value + over-reject; merged (see log row for commit)"),
    GapFingerprint("DL110", "C",
                   ("typecheck", "over_reject", "qualified-struct-construction"),
                   "qualified-struct-construction",
                   "fixed", "log #110; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL112", "C",
                   ("typecheck", "over_reject", "create-salt-literal"),
                   "create-salt-literal",
                   "fixed", "log #112; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL114", "S",
                   ("return_value", "dec-alloc-memptr", "wrong-value"),
                   "dec-alloc-memptr",
                   "fixed", "log #114; wrong-value; merged (see log row for commit)"),
    GapFingerprint("DL115", "C",
                   ("typecheck", "over_reject", "const-getter-pure-override"),
                   "const-getter-pure-override",
                   "fixed", "log #115; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL116", "C",
                   ("typecheck", "over_reject", "ternary-storage-statelvalue"),
                   "ternary-storage-statelvalue",
                   "fixed", "log #116; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL117", "S",
                   ("over_accept", "frac-cmp-overaccept", "over-accept"),
                   "frac-cmp-overaccept",
                   "fixed", "log #117; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL121", "C",
                   ("typecheck", "over_reject", "const-zero-bytesn"),
                   "const-zero-bytesn",
                   "fixed", "log #121; over-reject + over-accept; merged (see log row for commit)"),
    GapFingerprint("DL123", "S",
                   ("over_accept", "struct-cycle-fuel", "over-accept"),
                   "struct-cycle-fuel",
                   "fixed", "log #123; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL124", "S",
                   ("over_accept", "slice-dyn-base", "over-accept"),
                   "slice-dyn-base",
                   "fixed", "log #124; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL126", "C",
                   ("typecheck", "over_reject", "array-widen-copy"),
                   "array-widen-copy",
                   "fixed", "log #126; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL127", "S",
                   ("over_accept", "encodecall-overload", "over-accept"),
                   "encodecall-overload",
                   "fixed", "log #127; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL128", "S",
                   ("return_value", "abi-decode-eager-headcheck", "wrong-value"),
                   "abi-decode-eager-headcheck",
                   "fixed", "log #128; wrong-value; merged (see log row for commit)"),
    GapFingerprint("DL130", "S",
                   ("over_accept", "delete-expr-type", "over-accept"),
                   "delete-expr-type",
                   "fixed", "log #130; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL131", "C",
                   ("typecheck", "over_reject", "shortcircuit-call-pos"),
                   "shortcircuit-call-pos",
                   "fixed", "log #131; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL132", "S",
                   ("return_value", "tuple-write-order", "wrong-value"),
                   "tuple-write-order",
                   "fixed", "log #132; wrong-value; merged (see log row for commit)"),
    GapFingerprint("DL134", "C",
                   ("typecheck", "over_reject", "contract-ordered-cmp"),
                   "contract-ordered-cmp",
                   "fixed", "log #134; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL135", "C",
                   ("typecheck", "over_reject", "array-mutation-vs-usingfor"),
                   "array-mutation-vs-usingfor",
                   "fixed", "log #135; over-reject + over-accept; merged (see log row for commit)"),
    GapFingerprint("DL136", "S",
                   ("return_value", "qualified-error-collision", "wrong-value"),
                   "qualified-error-collision",
                   "fixed", "log #136; wrong-value; merged (see log row for commit)"),
    GapFingerprint("DL137", "C",
                   ("typecheck", "over_reject", "qualified-event-collision"),
                   "qualified-event-collision",
                   "fixed", "log #137; wrong-value + over-reject; merged (see log row for commit)"),
    GapFingerprint("DL138", "C",
                   ("typecheck", "over_reject", "qualified-event-selector"),
                   "qualified-event-selector",
                   "fixed", "log #138; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL139", "C",
                   ("typecheck", "over_reject", "error-selector-collision"),
                   "error-selector-collision",
                   "fixed", "log #139; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL140", "S",
                   ("return_value", "abiencode-lit-fixedbytes", "wrong-value"),
                   "abiencode-lit-fixedbytes",
                   "fixed", "log #140; wrong-value; merged (see log row for commit)"),
    GapFingerprint("DL141", "C",
                   ("typecheck", "over_reject", "emit-revert-lit-fixedbytes"),
                   "emit/revert-lit-fixedbytes",
                   "fixed", "log #141; wrong-value/over-reject; merged (see log row for commit)"),
    GapFingerprint("DL142", "S",
                   ("return_value", "push-lit-fixedbytes", "wrong-value"),
                   "push-lit-fixedbytes",
                   "fixed", "log #142; wrong-value; merged (see log row for commit)"),
    GapFingerprint("DL143", "C",
                   ("typecheck", "over_reject", "encwithselector-lit-selector"),
                   "encwithselector-lit-selector",
                   "fixed", "log #143; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL144", "S",
                   ("return_value", "extfnptr-call-lit-fixedbytes", "wrong-value"),
                   "extfnptr-call-lit-fixedbytes",
                   "fixed", "log #144; wrong-value; merged (see log row for commit)"),
    GapFingerprint("DL145", "C",
                   ("typecheck", "over_reject", "mapkey-lit-fixedbytes"),
                   "mapkey-lit-fixedbytes",
                   "fixed", "log #145; wrong-value/over-reject; merged (see log row for commit)"),
    GapFingerprint("DL148", "C",
                   ("typecheck", "over_reject", "call-in-array-literal"),
                   "call-in-array-literal",
                   "fixed", "log #148; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL149", "C",
                   ("typecheck", "over_reject", "call-in-struct-ctor-arg"),
                   "call-in-struct-ctor-arg",
                   "fixed", "log #149; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL150", "C",
                   ("typecheck", "over_reject", "call-in-new-arg"),
                   "call-in-new-arg",
                   "fixed", "log #150; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL151", "C",
                   ("typecheck", "over_reject", "call-in-nested-arg"),
                   "call-in-nested-arg",
                   "fixed", "log #151; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL152", "C",
                   ("typecheck", "over_reject", "stringconcat-hexlit-utf8"),
                   "stringconcat-hexlit-utf8",
                   "fixed", "log #152; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL154", "S",
                   ("over_accept", "deploy-abstract", "over-accept"),
                   "deploy-abstract",
                   "fixed", "log #154; over-accept; merged (see log row for commit)"),
    GapFingerprint("DL155", "C",
                   ("typecheck", "over_reject", "lib-storage-return"),
                   "lib-storage-return",
                   "fixed", "log #155; over-reject; merged (see log row for commit)"),
    GapFingerprint("DL160", "C",
                   ("typecheck", "over_reject", "recursive-struct-mem-construct"),
                   "recursive-struct-mem-construct",
                   "fixed", "log #160; over-reject/unimplemented; fix on main c027a5f"),
    GapFingerprint("DL163", "C",
                   ("typecheck", "over_reject", "new-contract-local-struct-array"),
                   "new-contract-local-struct-array",
                   "fixed", "log #163; over-reject; fix on main 001ff55"),
    GapFingerprint("DL164", "S",
                   ("return_value", "exp-narrow-base-wide-exponent", "wrong-value"),
                   "exp-narrow-base-wide-exponent",
                   "fixed", "log #164; wrong-value; fix on main a8da44e"),
    GapFingerprint("DL165", "C",
                   ("typecheck", "over_reject", "bool-cast-of-comparison"),
                   "bool-cast-of-comparison",
                   "fixed", "log #165; over-reject; fix on main 783c9ae"),
    GapFingerprint("DL166", "C",
                   ("typecheck", "over_reject", "overload-mem-vs-storage-location"),
                   "overload-mem-vs-storage-location",
                   "fixed", "log #166; over-reject; fix on main f60f910"),
    GapFingerprint("DL167", "C",
                   ("typecheck", "over_reject", "creationcode-ancestor"),
                   "creationcode-ancestor",
                   "fixed", "log #167; over-reject (+ over-accept bonus); fix on main ea8a519"),
    GapFingerprint("DL168", "S",
                   ("return_value", "delete-memory-nested-ref", "wrong-value"),
                   "delete-memory-nested-ref",
                   "fixed", "log #168; wrong-value; fix on main 2c74c40"),
    GapFingerprint("DL170", "C",
                   ("typecheck", "over_reject", "address-folded-const-conversion"),
                   "address-folded-const-conversion",
                   "fixed", "log #170; over-reject; fix on main df085d3"),
    GapFingerprint("DL171", "S",
                   ("return_value", "tuple-vardecl-from-abi-decode", "wrong-value"),
                   "tuple-vardecl-from-abi-decode",
                   "fixed", "log #171; wrong-value; fix on main 0a733a5"),
    GapFingerprint("DL172", "S",
                   ("return_value", "tuple-vardecl-ternary-rhs", "wrong-value"),
                   "tuple-vardecl-ternary-rhs",
                   "fixed", "log #172; wrong-value; fix on main 0a733a5"),
    GapFingerprint("DL173", "S",
                   ("return_value", "ternary-with-call-in-call-argument", "wrong-value"),
                   "ternary-with-call-in-call-argument",
                   "fixed", "log #173; wrong-value; fix on main d643539"),
    GapFingerprint("DL174", "S",
                   ("return_value", "abi-encode-internal-call-arg", "wrong-value"),
                   "abi-encode-internal-call-arg",
                   "fixed", "log #174; wrong-value; fix on main e6fa5da"),
    GapFingerprint("DL175", "S",
                   ("return_value", "bytesn-ident-index-panics", "wrong-value"),
                   "bytesn-ident-index-panics",
                   "fixed", "log #175; wrong-value; fix on main 61cef46; fix folded into the #176 merge (main 61cef46)"),
    GapFingerprint("DL176", "S",
                   ("return_value", "bytesn-storage-var-index-panic", "wrong-value"),
                   "bytesn-storage-var-index-panic",
                   "fixed", "log #176; wrong-value; fix on main 61cef46"),
    GapFingerprint("DL178", "S",
                   ("return_value", "enum-member-access-encodepacked-width", "wrong-value"),
                   "enum-member-access-encodepacked-width",
                   "fixed", "log #178; wrong-value; fix on main 07af1a0"),
    GapFingerprint("DL180", "C",
                   ("typecheck", "over_reject", "bytesn-eq-literal"),
                   "bytesn-eq-literal",
                   "fixed", "log #180; over-reject; fix on main 483032d"),
    GapFingerprint("DL181", "C",
                   ("typecheck", "over_reject", "address-nested-conv-const-depth3"),
                   "address-nested-conv-const-depth3",
                   "fixed", "log #181; over-reject; fix on main 4cd484e"),
    GapFingerprint("DL182", "S",
                   ("return_value", "forinit-narrow-counter-no-cleanup", "wrong-value"),
                   "forinit-narrow-counter-no-cleanup",
                   "fixed", "log #182; wrong-value/missing-panic; fix on main 08dfbe3"),
    GapFingerprint("DL183", "S",
                   ("return_value", "push-arg-narrow-no-cleanup", "wrong-value"),
                   "push-arg-narrow-no-cleanup",
                   "fixed", "log #183; wrong-value/missing-panic; fix on main 08dfbe3"),
    GapFingerprint("DL184", "S",
                   ("return_value", "struct-ctor-field-narrow-no-cleanup", "wrong-value"),
                   "struct-ctor-field-narrow-no-cleanup",
                   "fixed", "log #184; wrong-value/missing-panic; fix on main 08dfbe3"),
    GapFingerprint("DL185", "C",
                   ("typecheck", "over_reject", "array-literal-assign-unsupported"),
                   "array-literal-assign-unsupported",
                   "fixed", "log #185; over-reject; fix on main 53f0033"),
    GapFingerprint("DL187", "S",
                   ("return_value", "binary-operand-order-ltr", "wrong-value"),
                   "binary-operand-order-ltr",
                   "fixed", "log #187; wrong-value; fix on main 73e1567"),
    GapFingerprint("DL188", "C",
                   ("typecheck", "over_reject", "indexed-storage-ref-return-panic"),
                   "indexed-storage-ref-return-panic",
                   "fixed", "log #188; over-reject/spurious-revert; fix on main 8f0f3d3"),
    GapFingerprint("DL189", "S",
                   ("return_value", "tuple-rhs-component-order-rtl", "wrong-value"),
                   "tuple-rhs-component-order-rtl",
                   "fixed", "log #189; wrong-value; fix on main 73e1567"),
    GapFingerprint("DL190", "S",
                   ("return_value", "eval-order-l2r-sites", "wrong-value"),
                   "eval-order-l2r-sites",
                   "fixed", "log #190; wrong-value; fix on main 73e1567"),
    GapFingerprint("DL191", "S",
                   ("return_value", "external-binary-operand-order", "wrong-value"),
                   "external-binary-operand-order",
                   "fixed", "log #191; wrong-value; fix on main 73e1567"),
    GapFingerprint("DL192", "C",
                   ("typecheck", "over_reject", "hash-of-storage-bytes-panic"),
                   "hash-of-storage-bytes-panic",
                   "fixed", "log #192; over-reject/spurious-revert; fix on main 8f0f3d3"),
    GapFingerprint("DL194", "S",
                   ("return_value", "lvalue-index-key-narrow-no-cleanup", "wrong-value"),
                   "lvalue-index-key-narrow-no-cleanup",
                   "fixed", "log #194; wrong-value/missing-panic; fix on main 458f877"),
    GapFingerprint("DL195", "S",
                   ("return_value", "emit-call-args-defeat-two-phase", "wrong-value"),
                   "emit-call-args-defeat-two-phase",
                   "fixed", "log #195; wrong-value; fix on main 458f877"),
    GapFingerprint("DL197", "C",
                   ("typecheck", "over_reject", "inherited-struct-field-access"),
                   "inherited-struct-field-access",
                   "fixed", "log #197; over-reject; fix on main 1294798"),
    GapFingerprint("DL199", "C",
                   ("typecheck", "over_reject", "modifier-body-private-var-scope"),
                   "modifier-body-private-var-scope",
                   "fixed", "log #199; over-reject; fix on main 1294798"),
    GapFingerprint("DL205", "C",
                   ("typecheck", "over_reject", "ws1-env-audit-batch"),
                   "ws1-env-audit-batch",
                   "fixed", "log #205; wrong-value/over-reject; fix on main c3c0073"),
]

KNOWN_FIXED = KNOWN_FIXED + _DIVERGENCE_LOG_FIXED


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


def cluster_by_delta(lane: str, component: str, delta_shape: str) -> list[str]:
    """ADVISORY lane-S cluster hint: IDs of known-open gaps sharing the
    ADJUDICATOR-derived ``(observable_component, delta_shape)`` — elements 0 and 2
    of the lane-S fingerprint, which the submitter does NOT control (unlike the
    middle ``feature`` token that both ``match_fingerprint`` and ``match_relaxed``
    key on).

    Purpose (audit finding): a submitter can re-skin a KNOWN gap with a novel
    ``claim.feature`` string to dodge both matches and score it as novel
    (leaderboard novelty-inflation). This hint surfaces every known gap with the
    same observable delta family so a maintainer can spot the re-skin.

    ADVISORY ONLY — the caller must NOT turn this into ``duplicate_of``: deduping
    on the delta alone would OVER-CLUSTER genuinely distinct gaps (e.g. G2..G12
    all share ``(over_accept, over-accept)`` but are different mechanisms), and
    over-clustering would wrongly auto-deny a legitimately novel submission. Bias
    stays toward under-clustering; a human confirms."""
    if lane != "S":
        return []
    ids: list[str] = []
    for g in ALL_KNOWN:
        if g.status != "open" or g.lane != lane or len(g.key) < 3:
            continue
        if g.key[0] == component and g.key[2] == delta_shape:
            ids.append(g.id)
    return ids


def registry_summary() -> dict:
    return {
        "known_gaps_version": KNOWN_GAPS_VERSION,
        "open": [g.id for g in ALL_KNOWN if g.status == "open"],
        "fixed": [g.id for g in KNOWN_FIXED],
    }


if __name__ == "__main__":
    import json
    print(json.dumps(registry_summary(), indent=2))
