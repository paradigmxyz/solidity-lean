#!/usr/bin/env python3
"""Known-gaps registry (design §6.1b, §6.2) — DERIVED-KEY edition (v2).

WHAT CHANGED IN v2 (the registry redesign)
------------------------------------------
v1 keyed every entry on a HAND-WRITTEN slug tuple (``("typecheck",
"over_reject", "nested-tuple-LHS")``). The live adjudicator computes its
fingerprints from live engine output, so a hand-authored key could never
string-match a real submission — those rows were INERT (they never fired for
dedup) and could silently drift from reality. v2 designs that away:

  * Every entry carries its REPRO (``repro_dir``: a repo-relative directory of
    the Solidity source(s) exhibiting the gap — the corpus lane that pins it).
  * The entry's dedup KEY is DERIVED from that repro by the ONE canonical
    fingerprinter (``contest/fingerprint.py``) — never hand-authored. The
    derived keys are cached in ``contest/known_gap_fingerprints.json``
    (regenerate: ``python3 -m contest.known_gaps --rebuild``) and the registry
    invariant test in ``contest/run_samples.py`` re-derives every one at test
    time: stored-fingerprint == fingerprinter(entry.repro), or the suite fails
    loudly. Hand-editing a key or changing the fingerprinter cannot silently
    de-sync the registry again.
  * Entries whose repro could NOT be recovered carry ``repro_dir=None``: they
    keep their identity/metadata (nothing is dropped) but have NO key and are
    EXCLUDED from the auto-match path until a repro is added
    (``python3 -m contest.known_gaps --no-repro`` lists them).
  * Open gaps and known-fixed gaps use the SAME entry shape and the SAME
    derive-from-repro keying; they differ only by ``status``.

SOUNDNESS DIRECTION (unchanged, now structural)
-----------------------------------------------
This registry is the ANNOTATION / submission-time hint layer only. The
AUTHORITATIVE credit dedup is the fix-time replay (``contest/dedup_replay.py``,
keyed on engine-behavior-under-patch). Matching here can only UNDER-match:

  * ``match_submission`` fires only on an EXACT canonical-AST fingerprint match
    (the submission is the published repro up to renaming/reordering — a
    copy/re-skin). A genuinely novel program can never hash into it.
  * The v1 ``match_relaxed`` — which set ``duplicate_of`` from the
    SUBMITTER-CONTROLLED ``claim.feature`` slug and could thus wrongly tag a
    genuine novel find as a duplicate — is DEMOTED to ``feature_hint`` (an
    advisory list on the fingerprint evidence, never ``duplicate_of``).
  * ``cluster_by_delta`` stays advisory-only, as before.

So nothing in this module can auto-DENY credit for a genuine find; it can only
surface candidates to the human / the replay.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Optional


KNOWN_GAPS_VERSION = "2.0.0"  # registry redesign: hand-written slug keys ->
#                               repro-derived canonical fingerprints (fp1);
#                               no-repro entries excluded from auto-match.

_REPO_ROOT = Path(__file__).resolve().parent.parent
_FINGERPRINTS_FILE = Path(__file__).resolve().parent / "known_gap_fingerprints.json"


@dataclass(frozen=True)
class GapEntry:
    """One known gap. The dedup key is NOT stored here — it is derived from
    ``repro_dir`` by the canonical fingerprinter and cached in
    ``known_gap_fingerprints.json`` (invariant-tested)."""

    id: str                       # G1, CF3, DL175, ...
    lane: str                     # "C" | "S"
    status: str                   # "open" | "fixed"
    feature: str                  # short slug (advisory hint key, human-chosen)
    title: str                    # human-readable description
    component: str                # observable component / fail-stage family
    delta: str                    # delta class (over_reject / wrong-value /
    #                               over-accept / elab_reject / ...)
    repro_dir: Optional[str] = None  # repo-relative dir with the repro source(s)
    note: str = ""

    def repro_sources(self, repo_root: Optional[Path] = None) -> list[Path]:
        """The repro's .sol sources: ``<repro_dir>/src/*.sol`` if present, else
        ``<repro_dir>/*.sol`` (sorted; the fingerprint is file-order-invariant
        anyway)."""
        if not self.repro_dir:
            return []
        root = (repo_root or _REPO_ROOT) / self.repro_dir
        src = root / "src"
        base = src if src.is_dir() else root
        return sorted(base.glob("*.sol"))

    @property
    def fingerprint(self) -> Optional[str]:
        """The repro-derived canonical fingerprint (None for no-repro
        entries)."""
        return _fingerprints().get(self.id, {}).get("fingerprint")


# ---------------------------------------------------------------------------
# Entry tables. GENERATED-THEN-CURATED from the v1 registry: every v1 entry is
# preserved (identity, lane, feature slug, description, note); the old
# hand-written key tuple survives only as ADVISORY metadata (component/delta/
# feature) — never as a match key. ``repro_dir`` points at the corpus lane that
# pins the gap where one could be confidently located; entries with
# ``repro_dir=None`` await a repro (listed by --no-repro).
#
# Open-entry sources: docs/solidity-lean-solc-deep-comparison.md (G1-G22),
# rounds 2-12 review docs (CF3/CS1), docs/semantics-divergence-handoff.md
# (A1-A3, CB1 — OOS via X-EXTCALL in v1, recorded for v2).
# Fixed-entry sources: the v1 KNOWN_FIXED provenance list, incl. the
# DIVERGENCE-LOG reconciliation rows (DL52..DL205).
# ---------------------------------------------------------------------------

_OPEN_ENTRIES: list[GapEntry] = [
    GapEntry('G1', 'S', 'open', 'using-operator-nonbuiltin-body', 'user-defined operator runs as builtin instead of the operator fn', 'return_value', 'wrong-value', None, 'CONFIRMED wrong-value'),
    GapEntry('G2', 'S', 'open', 'msg.value-in-view-nonpayable', 'msg.value accepted in view/nonpayable functions', 'over_accept', 'over-accept', None),
    GapEntry('G3', 'S', 'open', 'eq-on-reference-types', '==/!= accepted on struct/array/bytes/string/mapping', 'over_accept', 'over-accept', None),
    GapEntry('G4', 'S', 'open', 'const-oob-index-bytesN-fixedarray', 'constant out-of-bounds index on bytesN / fixed array', 'over_accept', 'over-accept', None),
    GapEntry('G5', 'S', 'open', 'bare-return-with-named-returns', 'bare `return;` accepted with named returns', 'over_accept', 'over-accept', None),
    GapEntry('G6', 'S', 'open', 'super-to-unimplemented-base', 'super.f() resolves to an unimplemented abstract base fn', 'over_accept', 'over-accept', None),
    GapEntry('G7', 'S', 'open', 'emit-nonevent-member-callee', 'emit A.g() non-event member callee not validated', 'over_accept', 'over-accept', None),
    GapEntry('G8', 'S', 'open', 'revert-shadowing-member', 'revert E(args) with a same-arity shadowing member', 'over_accept', 'over-accept', None),
    GapEntry('G9', 'S', 'open', 'inline-array-literal-of-mapping', 'inline array literal of mapping type [m]', 'over_accept', 'over-accept', None),
    GapEntry('G10', 'S', 'open', 'msg.data-in-receive', 'msg.data in receive() not rejected', 'over_accept', 'over-accept', None),
    GapEntry('G11', 'S', 'open', 'cross-contract-creationcode-cycle', 'cross-contract creationCode/runtimeCode cycle undetected', 'over_accept', 'over-accept', None),
    GapEntry('G12', 'S', 'open', 'identifier-underscore-not-reserved', 'identifier name `_` not reserved', 'over_accept', 'over-accept', None),
    GapEntry('G13', 'C', 'open', 'nested-tuple-LHS', 'nested tuple LHS (((a,),)) = ((1,2),3);', 'typecheck', 'over_reject', 'tests/forge-harness/nested-tuple-assignment'),
    GapEntry('G14', 'C', 'open', 'storage-array-assign-shorter-source', 'storage array assignment with base-convertible/shorter source', 'typecheck', 'over_reject', 'tests/forge-harness/storage-array-copy-convert'),
    GapEntry('G15', 'C', 'open', 'ternary-of-literals-mobile-type', 'ternary-of-literals loses uint8 mobile common type', 'typecheck', 'over_reject', 'tests/forge-harness/ternary-literal-mobile-type'),
    GapEntry('G16', 'C', 'open', 'try-on-library-usingfor-call', 'try on a library / using-for call over-rejected', 'typecheck', 'over_reject', None),
    GapEntry('G17', 'S', 'open', 'storage-ctor-uninit-internal-fn-ptr', 'storage/ctor-stored uninitialized internal fn ptr Panic(0x51)', 'return_value', 'wrong-panic', 'tests/forge-harness/storage-uninit-fn-ptr'),
    GapEntry('G18', 'S', 'open', 'trycatch-multislot-extfnptr-return', 'try/catch binding of a multi-slot external-fn-ptr return', 'return_value', 'wrong-value', 'tests/forge-harness/try-external-fn-return'),
    GapEntry('G19', 'S', 'open', 'mutability-relaxing-override', 'mutability-relaxing overrides (virtual->view/pure)', 'over_accept', 'over-accept', None),
    GapEntry('G20', 'S', 'open', 'using-for-wildcard-imported', 'using ... for * wildcard imported but unexercised', 'over_accept', 'over-accept', None),
    GapEntry('G21', 'S', 'open', 'c99-block-scope-self-init', 'C99 block-scope activation incl. uint x = x; self-init', 'return_value', 'wrong-value', 'tests/forge-harness/c99-scope-activation'),
    GapEntry('G22', 'S', 'open', 'salted-create-address-prediction', 'saltedCreate address prediction (OOS-adjacent, needs initcode)', 'return_value', 'wrong-value', None, 'also covered by SEM-ADDR exclusion'),
    GapEntry('CF3', 'C', 'open', 'ctrlflow-fuel-placeholder-fallback', 'control-flow pointer-return analysis falls back to unsafeReturn on fuel exhaustion / bare modifier-placeholder (over-rejects deep bodies)', 'typecheck', 'over_reject', None, 'round 2 §3c; INFERRED, effectively unreachable; verify open/fixed'),
    GapEntry('CS1', 'S', 'open', 'selfdestruct-balance-transfer', 'selfdestruct records (from,recipient,deletesAccount) but does NOT move the balance (self not zeroed, recipient not credited)', 'return_value', 'wrong-value', 'tests/forge-harness/selfdestruct-balance', 'round 11 (doc -9); CONFIRMED-by-trace, reachability UNTESTED (live iff post-destruct balances are compared); verify open/fixed'),
    GapEntry('A1', 'S', 'open', 'try-void-call-codeless-address', 'try over a void external call to a codeless/EOA address: solidity-lean runs catch, solc reverts the caller uncatchably', 'revert_data', 'revert-vs-success', None, 'OOS via X-EXTCALL in v1; live for v2'),
    GapEntry('A2', 'S', 'open', 'catch-clause-source-order-vs-kind', 'catch-clause dispatch is source-order first-match; solc dispatches by kind (fallback catch listed first shadows Error/Panic)', 'return_value', 'wrong-value', 'tests/forge-harness/catch-dispatch-by-kind', 'OOS via X-EXTCALL in v1; live for v2'),
    GapEntry('A3', 'S', 'open', 'extcodesize-nonident-receiver', 'extcodesize existence check skipped for non-identifier receiver shapes (arr[i].f(), s.field.f(), m[k].f()) on a plain void call', 'revert_data', 'revert-vs-success', 'tests/forge-harness/extcodesize-existence-guard', 'OOS via X-EXTCALL in v1; live for v2'),
    GapEntry('CB1', 'S', 'open', 'trycatch-short-error-clause-dispatch', "try/catch Error(string) clause matches a short (<0x44 B) non-canonical Error-selector payload solc routes to catch(bytes): solidity-lean's strict codec lacks solc's returndatasize()>=0x44 gate -> wrong branch + value", 'return_value', 'wrong-value', None, 'round 9 (doc -8); OOS via X-EXTCALL in v1; live for v2'),
]

_FIXED_ENTRIES: list[GapEntry] = [
    GapEntry('DL1', 'S', 'fixed', 'storage-ctor-initializer-order', 'storage/constructor/initializer evaluation order = reverse-C3', 'return_value', 'wrong-value', None, 'fix commit 4d2a5c0'),
    GapEntry('M1', 'S', 'fixed', 'memory-alias-reference-assignment', 'memory reference-type assignment aliased (not deep-copied)', 'return_value', 'wrong-value', 'tests/forge-harness/memory-alias-fixes', 'fix commit ce58cfd (M1/M2/M3)'),
    GapEntry('M4', 'S', 'fixed', 'memory-deep-deref-encode-keccak', 'abi.encode/keccak of ref-nested memory deep-deref', 'return_value', 'wrong-value', None, 'fix commit 3043a9b (M4)'),
    GapEntry('E1', 'S', 'fixed', 'nonrational-immutable-read-in-pure', 'pure fn reading a non-rational-initialized immutable (keccak/abi/constant-ref) accepted; solc errors 2527 (View)', 'over_accept', 'over-accept', None, 'fix commit ce810e1 (rational-only immutable pure-read)'),
    GapEntry('E2', 'C', 'fixed', 'this-f-selector-in-pure', 'this.f.selector in a pure/non-view function over-rejected', 'typecheck', 'over_reject', None, 'fix commit 3c86aad'),
    GapEntry('O1', 'S', 'fixed', 'duplicate-contract-in-override-list', 'override(A, A) duplicate contract in the override list accepted; solc errors 4520', 'over_accept', 'over-accept', None, 'fix commit beba717'),
    GapEntry('CF2', 'C', 'fixed', 'no-revert-pruning-always-reverting-callee', 'pointer-return analysis lacked revert-pruning of always-reverting callees (over-reject); solc prunes via ControlFlowRevertPruner', 'typecheck', 'over_reject', 'tests/forge-harness/cf2-revert-pruning', 'fix commit 51959a7 (always-reverts fixpoint)'),
    GapEntry('PT1', 'S', 'fixed', 'constant-cyclic-dependency', 'self/mutually-cyclic `constant` accepted; solc errors 6161', 'over_accept', 'over-accept', None, 'fix commit ce810e1 (constantsHaveCycle)'),
    GapEntry('CL1', 'S', 'fixed', 'bare-modifier-base-ctor-zeroparam', 'bare modifier-style base-constructor call on a zero-param base accepted; solc errors 1563', 'over_accept', 'over-accept', None, 'fix commit 5cd1903 (hasArgList flag)'),
    GapEntry('PK1', 'C', 'fixed', 'encodepacked-nested-static-array', 'abi.encodePacked of a nested static value-array (uint[2][3]) over-rejected; solc encodes it', 'typecheck', 'over_reject', 'tests/forge-harness/packed-nested-static-array', 'fix commit 5cd1903 (nested-static-array encodePacked)'),
    GapEntry('UF1', 'C', 'fixed', 'using-for-global-nonudvt', 'using L/{f} for T global; on a struct/enum (non-UDVT user type) over-rejected; solc accepts', 'typecheck', 'over_reject', 'tests/forge-harness/using-for-global-nonudvt', 'fix commit 9cd70d3 (using-for global directive legality)'),
    GapEntry('UF2', 'S', 'fixed', 'operator-binding-mixed-params', 'operator binding whose fn params are not both the target type accepted at decl; solc errors 1884', 'over_accept', 'over-accept', None, 'fix commit 9cd70d3'),
    GapEntry('UF3', 'S', 'fixed', 'duplicate-operator-binding', 'duplicate operator binding for the same operator+type (never used) accepted; solc errors 4705', 'over_accept', 'over-accept', None, 'fix commit 9cd70d3'),
    GapEntry('V1', 'S', 'fixed', 'calldata-slice-oob-revert-data', "calldata-slice OOB (a[i:j]) reverted Panic(0x32) instead of solc's empty revert(0,0)", 'revert_data', 'wrong-revert', 'tests/forge-harness/calldata-slice-oob', 'fix commit db26356'),
    GapEntry('A1IF', 'C', 'fixed', 'abstract-contract-interfaceId-lowering', 'type(AbstractContract).interfaceId failed to lower (interface-only interfaceIdEnv) -> wrong-reject; solc computes it', 'elaboration', 'elab_reject', 'tests/forge-harness/abstract-interface-id', 'fix commit 3ed95f1 (round 6 A1; distinct from extcall A1)'),
    GapEntry('DL52', 'C', 'fixed', 'ec-cmp', 'ec-cmp', 'typecheck', 'over_reject', None, 'log #52; over-reject; merged (see log row for commit)'),
    GapEntry('DL53', 'S', 'fixed', 'fp-eq-2', 'fp-eq-2', 'return_value', 'wrong-value', None, 'log #53; wrong-value; merged (see log row for commit)'),
    GapEntry('DL54', 'S', 'fixed', 'mod-ret', 'mod-ret', 'over_accept', 'over-accept', None, 'log #54; over-accept; merged (see log row for commit)'),
    GapEntry('DL55', 'C', 'fixed', 'base-call', 'base-call', 'typecheck', 'over_reject', 'tests/forge-harness/base-qualified-call', 'log #55; over-reject; merged (see log row for commit)'),
    GapEntry('DL56', 'S', 'fixed', 'al1', 'al1', 'over_accept', 'over-accept', None, 'log #56; over-accept; merged (see log row for commit)'),
    GapEntry('DL57', 'C', 'fixed', 'tup-idx', 'tup-idx', 'typecheck', 'over_reject', None, 'log #57; over-reject; merged (see log row for commit)'),
    GapEntry('DL58', 'C', 'fixed', 'al-exec', 'al-exec', 'typecheck', 'over_reject', 'tests/forge-harness/inline-array-literal-exec', 'log #58; over-reject; merged (see log row for commit)'),
    GapEntry('DL59', 'S', 'fixed', 'uni1', 'uni1', 'return_value', 'wrong-value', None, 'log #59; wrong-value; merged (see log row for commit)'),
    GapEntry('DL62', 'S', 'fixed', 'dec-oom', 'dec-oom', 'return_value', 'wrong-value', None, 'log #62; wrong-value; merged (see log row for commit)'),
    GapEntry('DL63', 'S', 'fixed', 'get-struct', 'get-struct', 'over_accept', 'over-accept', None, 'log #63; over-accept + wrong-sig; merged (see log row for commit)'),
    GapEntry('DL69', 'S', 'fixed', 'priv-shadow', 'priv-shadow', 'over_accept', 'over-accept', None, 'log #69; over-accept; merged (see log row for commit)'),
    GapEntry('DL70', 'C', 'fixed', 'callpos-family', 'callpos-family', 'typecheck', 'over_reject', 'tests/forge-harness/callpos-family', 'log #70; over-reject; merged (see log row for commit)'),
    GapEntry('DL70b', 'C', 'fixed', 'call-position', 'call-position', 'typecheck', 'over_reject', 'tests/forge-harness/call-position', 'log #70; over-reject; merged (see log row for commit)'),
    GapEntry('DL73', 'C', 'fixed', 'extcall-binary', 'extcall-binary', 'typecheck', 'over_reject', 'tests/forge-harness/extcall-binary', 'log #73; over-reject; merged (see log row for commit)'),
    GapEntry('DL74', 'C', 'fixed', 'emit-qual', 'emit-qual', 'typecheck', 'over_reject', None, 'log #74; over-reject; merged (see log row for commit)'),
    GapEntry('DL77', 'C', 'fixed', 'revert-qual', 'revert-qual', 'typecheck', 'over_reject', None, 'log #77; over-reject; merged (see log row for commit)'),
    GapEntry('DL78', 'S', 'fixed', 'encpacked-lit', 'encpacked-lit', 'over_accept', 'over-accept', 'tests/forge-harness/encpacked-literal', 'log #78; over-accept; merged (see log row for commit)'),
    GapEntry('DL80', 'C', 'fixed', 'sb-a', 'sb-a', 'typecheck', 'over_reject', None, 'log #80; over-reject; merged (see log row for commit)'),
    GapEntry('DL81', 'S', 'fixed', 'div-dup-inh-mod', 'div-dup-inh-mod', 'over_accept', 'over-accept', None, 'log #81; over-accept; merged (see log row for commit)'),
    GapEntry('DL82', 'S', 'fixed', 'usingfor-brace', 'usingfor-brace', 'over_accept', 'over-accept', None, 'log #82; over-accept; merged (see log row for commit)'),
    GapEntry('DL83', 'S', 'fixed', 'd-oom-dispatch', 'd-oom-dispatch', 'return_value', 'wrong-value', 'tests/forge-harness/dispatch-oom', 'log #83; wrong-value; merged (see log row for commit)'),
    GapEntry('DL84', 'S', 'fixed', 'tc-oom1', 'tc-oom1', 'return_value', 'wrong-value', None, 'log #84; wrong-value; merged (see log row for commit)'),
    GapEntry('DL86', 'S', 'fixed', 'cmp-mixedsign', 'cmp-mixedsign', 'over_accept', 'over-accept', None, 'log #86; over-accept; merged (see log row for commit)'),
    GapEntry('DL93', 'C', 'fixed', 'lib-storage-public-2', 'lib-storage-public-2', 'typecheck', 'over_reject', 'tests/forge-harness/lib-storage-public-2', 'log #93; over-reject; merged (see log row for commit)'),
    GapEntry('DL94', 'S', 'fixed', 'str-overaccept---payable-vis', 'str-overaccept / payable-vis', 'over_accept', 'over-accept', None, 'log #94; over-accept; merged (see log row for commit)'),
    GapEntry('DL95', 'C', 'fixed', 'push-field-lvalue', 'push-field-lvalue', 'typecheck', 'over_reject', 'tests/forge-harness/push-field-lvalue', 'log #95; over-reject; merged (see log row for commit)'),
    GapEntry('DL101', 'C', 'fixed', 'calldata-lazy-value', 'calldata-lazy-value', 'typecheck', 'over_reject', 'tests/forge-harness/calldata-lazy-value', 'log #101; over-reject; merged (see log row for commit)'),
    GapEntry('DL102', 'C', 'fixed', 'qualified-member-cluster', 'qualified-member cluster', 'typecheck', 'over_reject', 'tests/forge-harness/qualified-member', 'log #102; over-reject; merged (see log row for commit)'),
    GapEntry('DL104', 'S', 'fixed', 'syntax-overaccept', 'syntax-overaccept', 'over_accept', 'over-accept', None, 'log #104; over-accept; merged (see log row for commit)'),
    GapEntry('DL105', 'S', 'fixed', 'dup-event-sibling', 'dup-event-sibling', 'over_accept', 'over-accept', None, 'log #105; over-accept; merged (see log row for commit)'),
    GapEntry('DL106', 'S', 'fixed', 'inherited-identifier-clash', 'inherited-identifier-clash', 'over_accept', 'over-accept', None, 'log #106; over-accept; merged (see log row for commit)'),
    GapEntry('DL108', 'S', 'fixed', 'abi-decode-address-payable', 'abi-decode-address-payable', 'return_value', 'wrong-value', 'tests/forge-harness/abi-decode-address-payable', 'log #108; wrong-value; merged (see log row for commit)'),
    GapEntry('DL109', 'C', 'fixed', 'common-type-literal-mobile', 'common-type-literal-mobile', 'typecheck', 'over_reject', 'tests/forge-harness/common-type-literal', 'log #109; wrong-value + over-reject; merged (see log row for commit)'),
    GapEntry('DL110', 'C', 'fixed', 'qualified-struct-construction', 'qualified-struct-construction', 'typecheck', 'over_reject', 'tests/forge-harness/qualified-struct-construction', 'log #110; over-reject; merged (see log row for commit)'),
    GapEntry('DL112', 'C', 'fixed', 'create-salt-literal', 'create-salt-literal', 'typecheck', 'over_reject', 'tests/forge-harness/create-salt-literal', 'log #112; over-reject; merged (see log row for commit)'),
    GapEntry('DL114', 'S', 'fixed', 'dec-alloc-memptr', 'dec-alloc-memptr', 'return_value', 'wrong-value', 'tests/forge-harness/dec-alloc-memptr', 'log #114; wrong-value; merged (see log row for commit)'),
    GapEntry('DL115', 'C', 'fixed', 'const-getter-pure-override', 'const-getter-pure-override', 'typecheck', 'over_reject', 'tests/forge-harness/const-getter-pure-override', 'log #115; over-reject; merged (see log row for commit)'),
    GapEntry('DL116', 'C', 'fixed', 'ternary-storage-statelvalue', 'ternary-storage-statelvalue', 'typecheck', 'over_reject', None, 'log #116; over-reject; merged (see log row for commit)'),
    GapEntry('DL117', 'S', 'fixed', 'frac-cmp-overaccept', 'frac-cmp-overaccept', 'over_accept', 'over-accept', None, 'log #117; over-accept; merged (see log row for commit)'),
    GapEntry('DL121', 'C', 'fixed', 'const-zero-bytesn', 'const-zero-bytesn', 'typecheck', 'over_reject', 'tests/forge-harness/const-zero-bytesn', 'log #121; over-reject + over-accept; merged (see log row for commit)'),
    GapEntry('DL123', 'S', 'fixed', 'struct-cycle-fuel', 'struct-cycle-fuel', 'over_accept', 'over-accept', None, 'log #123; over-accept; merged (see log row for commit)'),
    GapEntry('DL124', 'S', 'fixed', 'slice-dyn-base', 'slice-dyn-base', 'over_accept', 'over-accept', None, 'log #124; over-accept; merged (see log row for commit)'),
    GapEntry('DL126', 'C', 'fixed', 'array-widen-copy', 'array-widen-copy', 'typecheck', 'over_reject', 'tests/forge-harness/array-widen-copy', 'log #126; over-reject; merged (see log row for commit)'),
    GapEntry('DL127', 'S', 'fixed', 'encodecall-overload', 'encodecall-overload', 'over_accept', 'over-accept', None, 'log #127; over-accept; merged (see log row for commit)'),
    GapEntry('DL128', 'S', 'fixed', 'abi-decode-eager-headcheck', 'abi-decode-eager-headcheck', 'return_value', 'wrong-value', 'tests/forge-harness/abi-memory-eager', 'log #128; wrong-value; merged (see log row for commit)'),
    GapEntry('DL130', 'S', 'fixed', 'delete-expr-type', 'delete-expr-type', 'over_accept', 'over-accept', None, 'log #130; over-accept; merged (see log row for commit)'),
    GapEntry('DL131', 'C', 'fixed', 'shortcircuit-call-pos', 'shortcircuit-call-pos', 'typecheck', 'over_reject', 'tests/forge-harness/shortcircuit-callpos', 'log #131; over-reject; merged (see log row for commit)'),
    GapEntry('DL132', 'S', 'fixed', 'tuple-write-order', 'tuple-write-order', 'return_value', 'wrong-value', 'tests/forge-harness/tuple-write-order', 'log #132; wrong-value; merged (see log row for commit)'),
    GapEntry('DL134', 'C', 'fixed', 'contract-ordered-cmp', 'contract-ordered-cmp', 'typecheck', 'over_reject', 'tests/forge-harness/contract-ordered-compare', 'log #134; over-reject; merged (see log row for commit)'),
    GapEntry('DL135', 'C', 'fixed', 'array-mutation-vs-usingfor', 'array-mutation-vs-usingfor', 'typecheck', 'over_reject', 'tests/forge-harness/array-mutation-usingfor', 'log #135; over-reject + over-accept; merged (see log row for commit)'),
    GapEntry('DL136', 'S', 'fixed', 'qualified-error-collision', 'qualified-error-collision', 'return_value', 'wrong-value', None, 'log #136; wrong-value; merged (see log row for commit)'),
    GapEntry('DL137', 'C', 'fixed', 'qualified-event-collision', 'qualified-event-collision', 'typecheck', 'over_reject', None, 'log #137; wrong-value + over-reject; merged (see log row for commit)'),
    GapEntry('DL138', 'C', 'fixed', 'qualified-event-selector', 'qualified-event-selector', 'typecheck', 'over_reject', 'tests/forge-harness/qualified-event-selector', 'log #138; over-reject; merged (see log row for commit)'),
    GapEntry('DL139', 'C', 'fixed', 'error-selector-collision', 'error-selector-collision', 'typecheck', 'over_reject', 'tests/forge-harness/error-selector-collision', 'log #139; over-reject; merged (see log row for commit)'),
    GapEntry('DL140', 'S', 'fixed', 'abiencode-lit-fixedbytes', 'abiencode-lit-fixedbytes', 'return_value', 'wrong-value', 'tests/forge-harness/abiencode-lit-fixedbytes', 'log #140; wrong-value; merged (see log row for commit)'),
    GapEntry('DL141', 'C', 'fixed', 'emit-revert-lit-fixedbytes', 'emit/revert-lit-fixedbytes', 'typecheck', 'over_reject', None, 'log #141; wrong-value/over-reject; merged (see log row for commit)'),
    GapEntry('DL142', 'S', 'fixed', 'push-lit-fixedbytes', 'push-lit-fixedbytes', 'return_value', 'wrong-value', None, 'log #142; wrong-value; merged (see log row for commit)'),
    GapEntry('DL143', 'C', 'fixed', 'encwithselector-lit-selector', 'encwithselector-lit-selector', 'typecheck', 'over_reject', None, 'log #143; over-reject; merged (see log row for commit)'),
    GapEntry('DL144', 'S', 'fixed', 'extfnptr-call-lit-fixedbytes', 'extfnptr-call-lit-fixedbytes', 'return_value', 'wrong-value', None, 'log #144; wrong-value; merged (see log row for commit)'),
    GapEntry('DL145', 'C', 'fixed', 'mapkey-lit-fixedbytes', 'mapkey-lit-fixedbytes', 'typecheck', 'over_reject', None, 'log #145; wrong-value/over-reject; merged (see log row for commit)'),
    GapEntry('DL148', 'C', 'fixed', 'call-in-array-literal', 'call-in-array-literal', 'typecheck', 'over_reject', None, 'log #148; over-reject; merged (see log row for commit)'),
    GapEntry('DL149', 'C', 'fixed', 'call-in-struct-ctor-arg', 'call-in-struct-ctor-arg', 'typecheck', 'over_reject', None, 'log #149; over-reject; merged (see log row for commit)'),
    GapEntry('DL150', 'C', 'fixed', 'call-in-new-arg', 'call-in-new-arg', 'typecheck', 'over_reject', None, 'log #150; over-reject; merged (see log row for commit)'),
    GapEntry('DL151', 'C', 'fixed', 'call-in-nested-arg', 'call-in-nested-arg', 'typecheck', 'over_reject', None, 'log #151; over-reject; merged (see log row for commit)'),
    GapEntry('DL152', 'C', 'fixed', 'stringconcat-hexlit-utf8', 'stringconcat-hexlit-utf8', 'typecheck', 'over_reject', 'tests/forge-harness/stringconcat-hexlit', 'log #152; over-reject; merged (see log row for commit)'),
    GapEntry('DL154', 'S', 'fixed', 'deploy-abstract', 'deploy-abstract', 'over_accept', 'over-accept', None, 'log #154; over-accept; merged (see log row for commit)'),
    GapEntry('DL155', 'C', 'fixed', 'lib-storage-return', 'lib-storage-return', 'typecheck', 'over_reject', 'tests/forge-harness/lib-storage-return', 'log #155; over-reject; merged (see log row for commit)'),
    GapEntry('DL160', 'C', 'fixed', 'recursive-struct-mem-construct', 'recursive-struct-mem-construct', 'typecheck', 'over_reject', 'tests/forge-harness/recursive-struct-mem-construct', 'log #160; over-reject/unimplemented; fix on main c027a5f'),
    GapEntry('DL163', 'C', 'fixed', 'new-contract-local-struct-array', 'new-contract-local-struct-array', 'typecheck', 'over_reject', 'tests/forge-harness/new-contract-local-struct-array', 'log #163; over-reject; fix on main 001ff55'),
    GapEntry('DL164', 'S', 'fixed', 'exp-narrow-base-wide-exponent', 'exp-narrow-base-wide-exponent', 'return_value', 'wrong-value', 'tests/forge-harness/exp-narrow-base-wide-exp', 'log #164; wrong-value; fix on main a8da44e'),
    GapEntry('DL165', 'C', 'fixed', 'bool-cast-of-comparison', 'bool-cast-of-comparison', 'typecheck', 'over_reject', 'tests/forge-harness/bool-cast-of-comparison', 'log #165; over-reject; fix on main 783c9ae'),
    GapEntry('DL166', 'C', 'fixed', 'overload-mem-vs-storage-location', 'overload-mem-vs-storage-location', 'typecheck', 'over_reject', 'tests/forge-harness/overload-mem-vs-storage', 'log #166; over-reject; fix on main f60f910'),
    GapEntry('DL167', 'C', 'fixed', 'creationcode-ancestor', 'creationcode-ancestor', 'typecheck', 'over_reject', 'tests/forge-harness/creationcode-ancestor', 'log #167; over-reject (+ over-accept bonus); fix on main ea8a519'),
    GapEntry('DL168', 'S', 'fixed', 'delete-memory-nested-ref', 'delete-memory-nested-ref', 'return_value', 'wrong-value', 'tests/forge-harness/delete-memory-nested-ref', 'log #168; wrong-value; fix on main 2c74c40'),
    GapEntry('DL170', 'C', 'fixed', 'address-folded-const-conversion', 'address-folded-const-conversion', 'typecheck', 'over_reject', 'tests/forge-harness/address-folded-const', 'log #170; over-reject; fix on main df085d3'),
    GapEntry('DL171', 'S', 'fixed', 'tuple-vardecl-from-abi-decode', 'tuple-vardecl-from-abi-decode', 'return_value', 'wrong-value', 'tests/forge-harness/tuple-vardecl-abi-decode', 'log #171; wrong-value; fix on main 0a733a5'),
    GapEntry('DL172', 'S', 'fixed', 'tuple-vardecl-ternary-rhs', 'tuple-vardecl-ternary-rhs', 'return_value', 'wrong-value', 'tests/forge-harness/tuple-vardecl-ternary', 'log #172; wrong-value; fix on main 0a733a5'),
    GapEntry('DL173', 'S', 'fixed', 'ternary-with-call-in-call-argument', 'ternary-with-call-in-call-argument', 'return_value', 'wrong-value', 'tests/forge-harness/ternary-call-in-arg', 'log #173; wrong-value; fix on main d643539'),
    GapEntry('DL174', 'S', 'fixed', 'abi-encode-internal-call-arg', 'abi-encode-internal-call-arg', 'return_value', 'wrong-value', 'tests/forge-harness/abi-encode-call-arg', 'log #174; wrong-value; fix on main e6fa5da'),
    GapEntry('DL175', 'S', 'fixed', 'bytesn-ident-index-panics', 'bytesn-ident-index-panics', 'return_value', 'wrong-value', 'tests/forge-harness/bytesn-ident-index', 'log #175; wrong-value; fix on main 61cef46; fix folded into the #176 merge (main 61cef46)'),
    GapEntry('DL176', 'S', 'fixed', 'bytesn-storage-var-index-panic', 'bytesn-storage-var-index-panic', 'return_value', 'wrong-value', 'tests/forge-harness/bytesn-ident-index', 'log #176; wrong-value; fix on main 61cef46; repro shared with DL175 (one folded fix/lane)'),
    GapEntry('DL178', 'S', 'fixed', 'enum-member-access-encodepacked-width', 'enum-member-access-encodepacked-width', 'return_value', 'wrong-value', 'tests/forge-harness/enum-member-encodepacked', 'log #178; wrong-value; fix on main 07af1a0'),
    GapEntry('DL180', 'C', 'fixed', 'bytesn-eq-literal', 'bytesn-eq-literal', 'typecheck', 'over_reject', 'tests/forge-harness/bytesn-eq-literal', 'log #180; over-reject; fix on main 483032d'),
    GapEntry('DL181', 'C', 'fixed', 'address-nested-conv-const-depth3', 'address-nested-conv-const-depth3', 'typecheck', 'over_reject', 'tests/forge-harness/address-nested-conv', 'log #181; over-reject; fix on main 4cd484e'),
    GapEntry('DL182', 'S', 'fixed', 'forinit-narrow-counter-no-cleanup', 'forinit-narrow-counter-no-cleanup', 'return_value', 'wrong-value', 'tests/forge-harness/narrow-cleanup-family', 'log #182; wrong-value/missing-panic; fix on main 08dfbe3; family lane shared by DL182/183/184/194'),
    GapEntry('DL183', 'S', 'fixed', 'push-arg-narrow-no-cleanup', 'push-arg-narrow-no-cleanup', 'return_value', 'wrong-value', 'tests/forge-harness/narrow-cleanup-family', 'log #183; wrong-value/missing-panic; fix on main 08dfbe3; family lane shared by DL182/183/184/194'),
    GapEntry('DL184', 'S', 'fixed', 'struct-ctor-field-narrow-no-cleanup', 'struct-ctor-field-narrow-no-cleanup', 'return_value', 'wrong-value', 'tests/forge-harness/narrow-cleanup-family', 'log #184; wrong-value/missing-panic; fix on main 08dfbe3; family lane shared by DL182/183/184/194'),
    GapEntry('DL185', 'C', 'fixed', 'array-literal-assign-unsupported', 'array-literal-assign-unsupported', 'typecheck', 'over_reject', None, 'log #185; over-reject; fix on main 53f0033'),
    GapEntry('DL187', 'S', 'fixed', 'binary-operand-order-ltr', 'binary-operand-order-ltr', 'return_value', 'wrong-value', None, 'log #187; wrong-value; fix on main 73e1567'),
    GapEntry('DL188', 'C', 'fixed', 'indexed-storage-ref-return-panic', 'indexed-storage-ref-return-panic', 'typecheck', 'over_reject', None, 'log #188; over-reject/spurious-revert; fix on main 8f0f3d3'),
    GapEntry('DL189', 'S', 'fixed', 'tuple-rhs-component-order-rtl', 'tuple-rhs-component-order-rtl', 'return_value', 'wrong-value', None, 'log #189; wrong-value; fix on main 73e1567'),
    GapEntry('DL190', 'S', 'fixed', 'eval-order-l2r-sites', 'eval-order-l2r-sites', 'return_value', 'wrong-value', None, 'log #190; wrong-value; fix on main 73e1567'),
    GapEntry('DL191', 'S', 'fixed', 'external-binary-operand-order', 'external-binary-operand-order', 'return_value', 'wrong-value', None, 'log #191; wrong-value; fix on main 73e1567'),
    GapEntry('DL192', 'C', 'fixed', 'hash-of-storage-bytes-panic', 'hash-of-storage-bytes-panic', 'typecheck', 'over_reject', None, 'log #192; over-reject/spurious-revert; fix on main 8f0f3d3'),
    GapEntry('DL194', 'S', 'fixed', 'lvalue-index-key-narrow-no-cleanup', 'lvalue-index-key-narrow-no-cleanup', 'return_value', 'wrong-value', 'tests/forge-harness/narrow-cleanup-family', 'log #194; wrong-value/missing-panic; fix on main 458f877; family lane shared by DL182/183/184/194'),
    GapEntry('DL195', 'S', 'fixed', 'emit-call-args-defeat-two-phase', 'emit-call-args-defeat-two-phase', 'return_value', 'wrong-value', None, 'log #195; wrong-value; fix on main 458f877'),
    GapEntry('DL197', 'C', 'fixed', 'inherited-struct-field-access', 'inherited-struct-field-access', 'typecheck', 'over_reject', 'tests/forge-harness/inherited-struct-field', 'log #197; over-reject; fix on main 1294798'),
    GapEntry('DL199', 'C', 'fixed', 'modifier-body-private-var-scope', 'modifier-body-private-var-scope', 'typecheck', 'over_reject', 'tests/forge-harness/modifier-private-scope', 'log #199; over-reject; fix on main 1294798'),
    GapEntry('DL205', 'C', 'fixed', 'ws1-env-audit-batch', 'ws1-env-audit-batch', 'typecheck', 'over_reject', None, 'log #205; wrong-value/over-reject; fix on main c3c0073'),
]


# Back-compat aliases (consumers iterate these): ALL_KNOWN = the open index,
# KNOWN_FIXED = the fixed/provenance list. Same objects, same names as v1.
ALL_KNOWN: list[GapEntry] = _OPEN_ENTRIES
KNOWN_FIXED: list[GapEntry] = _FIXED_ENTRIES
_ALL_ENTRIES: list[GapEntry] = _OPEN_ENTRIES + _FIXED_ENTRIES


# ---------------------------------------------------------------------------
# Derived-fingerprint cache (generated by --rebuild, verified by the registry
# invariant test).
# ---------------------------------------------------------------------------

_FP_CACHE: Optional[dict[str, dict[str, Any]]] = None


def _fingerprints() -> dict[str, dict[str, Any]]:
    global _FP_CACHE
    if _FP_CACHE is None:
        try:
            data = json.loads(_FINGERPRINTS_FILE.read_text())
            _FP_CACHE = data.get("entries", {})
        except (OSError, json.JSONDecodeError):
            _FP_CACHE = {}
    return _FP_CACHE


def derive_fingerprint(entry: GapEntry, solc: Optional[str] = None,
                       repo_root: Optional[Path] = None) -> Optional[str]:
    """Run the entry's repro through the ONE canonical fingerprinter. None for
    a no-repro entry. This is the single source of truth for registry keys."""
    sources = entry.repro_sources(repo_root)
    if not sources:
        return None
    from . import fingerprint as fpm
    return fpm.repro_fingerprint(entry.lane, entry.delta, sources, solc)


def rebuild_fingerprints(solc: Optional[str] = None,
                         repo_root: Optional[Path] = None) -> dict[str, Any]:
    """Recompute every entry's derived fingerprint and rewrite the cache file.
    Returns the written document."""
    from . import fingerprint as fpm
    entries: dict[str, Any] = {}
    for e in _ALL_ENTRIES:
        fp = derive_fingerprint(e, solc, repo_root)
        if fp is not None:
            entries[e.id] = {
                "fingerprint": fp,
                "repro_dir": e.repro_dir,
                "sources": [p.name for p in e.repro_sources(repo_root)],
            }
    doc = {
        "scheme": fpm.FINGERPRINT_SCHEME,
        "known_gaps_version": KNOWN_GAPS_VERSION,
        "note": "GENERATED by `python3 -m contest.known_gaps --rebuild` — do "
                "not hand-edit. Every fingerprint is derived from its entry's "
                "repro by contest/fingerprint.py; the registry invariant test "
                "re-derives and cross-checks all of them.",
        "entries": entries,
    }
    _FINGERPRINTS_FILE.write_text(json.dumps(doc, indent=2, sort_keys=True) + "\n")
    global _FP_CACHE
    _FP_CACHE = entries
    return doc


def verify_fingerprints(solc: Optional[str] = None,
                        repo_root: Optional[Path] = None) -> list[str]:
    """THE REGISTRY INVARIANT: for every entry, stored-fingerprint ==
    fingerprinter(entry.repro); no-repro entries must have NO stored key.
    Returns a list of human-readable violations (empty == invariant holds)."""
    problems: list[str] = []
    stored = _fingerprints()
    seen_ids: set[str] = set()
    for e in _ALL_ENTRIES:
        if e.id in seen_ids:
            problems.append(f"{e.id}: duplicate entry id")
        seen_ids.add(e.id)
        if e.lane not in ("C", "S"):
            problems.append(f"{e.id}: bad lane {e.lane!r}")
        if e.status not in ("open", "fixed"):
            problems.append(f"{e.id}: bad status {e.status!r}")
        if not e.repro_dir:
            if e.id in stored:
                problems.append(
                    f"{e.id}: no-repro entry has a stored fingerprint "
                    "(keys must be derived, never hand-authored)")
            continue
        sources = e.repro_sources(repo_root)
        if not sources:
            problems.append(f"{e.id}: repro_dir {e.repro_dir!r} has no .sol sources")
            continue
        derived = derive_fingerprint(e, solc, repo_root)
        got = stored.get(e.id, {}).get("fingerprint")
        if got is None:
            problems.append(f"{e.id}: repro present but no stored fingerprint "
                            "(run --rebuild)")
        elif got != derived:
            problems.append(
                f"{e.id}: stored fingerprint {got!r} != derived {derived!r} "
                "(registry de-synced from the fingerprinter — run --rebuild "
                "and review)")
    for k in stored:
        if k not in seen_ids:
            problems.append(f"{k}: stored fingerprint for unknown entry id")
    return problems


# ---------------------------------------------------------------------------
# Matching — the submission-time hint layer (UNDER-matching by construction).
# ---------------------------------------------------------------------------

def delta_class_of_live_key(lane: str, key: tuple) -> str:
    """Map the adjudicator's LIVE §6.2 fingerprint tuple to the delta class the
    registry keys on. Mirrors adjudicate's classification exactly:
    lane C -> the reason class (element 1: over_reject / elab_reject /
    unimplemented / ...); lane S -> the differing component (element 2:
    wrong-value / over-accept / ...)."""
    if lane == "C":
        return str(key[1]) if len(key) > 1 else "unknown"
    return str(key[2]) if len(key) > 2 else "unknown"


def match_submission(lane: str, live_key: tuple, submission_root: Path,
                     solc: Optional[str] = None) -> Optional[GapEntry]:
    """EXACT-repro dedup: fingerprint the submission's own sources with the
    canonical fingerprinter and match against the derived keys of KNOWN-OPEN
    entries. Fires only when the submission is a published repro up to
    renaming / reordering / cosmetic variation — the conservative direction
    (a novel program can never hash-collide in). Returns None on any doubt
    (missing sources, solc failure, no match)."""
    try:
        src_dir = Path(submission_root) / "src"
        sources = sorted(src_dir.glob("*.sol")) if src_dir.is_dir() else []
        if not sources:
            return None
        from . import fingerprint as fpm
        fp = fpm.repro_fingerprint(
            lane, delta_class_of_live_key(lane, live_key), sources, solc)
    except Exception:
        return None  # hint layer: never let matching break adjudication
    for e in _OPEN_ENTRIES:
        if e.lane == lane and e.fingerprint is not None and e.fingerprint == fp:
            return e
    return None


def feature_hint(lane: str, feature_token: str) -> list[str]:
    """ADVISORY ONLY (v1's match_relaxed, demoted): ids of known-open gaps
    whose curated feature slug equals the given token. The token is
    SUBMITTER-CONTROLLED for lane S, so this must never set ``duplicate_of``
    — a submitter reusing a published slug on a genuinely novel find would be
    wrongly tagged a duplicate (auto-deny, the forbidden direction). Surfaced
    on the report fingerprint for the maintainer instead."""
    return [e.id for e in _OPEN_ENTRIES
            if e.lane == lane and e.feature == feature_token]


def cluster_by_delta(lane: str, component: str, delta_shape: str) -> list[str]:
    """ADVISORY lane-S cluster hint (unchanged from v1): IDs of known-open gaps
    sharing the ADJUDICATOR-derived ``(observable_component, delta_shape)``.
    Never sets ``duplicate_of`` — the delta alone over-clusters genuinely
    distinct gaps (e.g. every over-accept shares one delta family); bias stays
    toward under-clustering, a human confirms."""
    if lane != "S":
        return []
    return [e.id for e in _OPEN_ENTRIES
            if e.lane == lane and e.component == component
            and e.delta == delta_shape]


def no_repro_entries() -> list[GapEntry]:
    """Entries excluded from the auto-match path until a repro is recovered."""
    return [e for e in _ALL_ENTRIES if not e.repro_dir]


def registry_summary() -> dict:
    stored = _fingerprints()
    return {
        "known_gaps_version": KNOWN_GAPS_VERSION,
        "open": [e.id for e in ALL_KNOWN],
        "fixed": [e.id for e in KNOWN_FIXED],
        "keyed": sorted(stored.keys()),
        "no_repro": [e.id for e in no_repro_entries()],
    }


def _main(argv: Optional[list[str]] = None) -> int:
    import argparse
    p = argparse.ArgumentParser(description="Known-gaps registry tool")
    p.add_argument("--rebuild", action="store_true",
                   help="re-derive every fingerprint from its repro and "
                        "rewrite known_gap_fingerprints.json")
    p.add_argument("--check", action="store_true",
                   help="verify the invariant: stored == derived for all")
    p.add_argument("--no-repro", action="store_true",
                   help="list entries awaiting a repro (excluded from "
                        "auto-match)")
    p.add_argument("--solc", default=None)
    args = p.parse_args(argv)
    if args.rebuild:
        doc = rebuild_fingerprints(args.solc)
        print(f"rebuilt {len(doc['entries'])} derived fingerprints -> "
              f"{_FINGERPRINTS_FILE.name}")
        return 0
    if args.check:
        problems = verify_fingerprints(args.solc)
        for pr in problems:
            print(f"VIOLATION: {pr}")
        print("invariant OK" if not problems else
              f"{len(problems)} violation(s)")
        return 0 if not problems else 1
    if args.no_repro:
        for e in no_repro_entries():
            print(f"{e.id}\t{e.status}\tlane {e.lane}\t{e.feature}")
        return 0
    print(json.dumps(registry_summary(), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())
