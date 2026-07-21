#!/usr/bin/env python3
"""Adjudicator - the two-lane decision tree (design §4) and CLI entrypoint.

    python -m contest.adjudicate <submission-dir>

A submission directory (design §5.1):

    submission/
      src/*.sol              flattened source(s), NO import directives
      test/*.t.sol           a Forge test asserting the REAL solc+EVM behavior
      foundry.toml           minimal Foundry project config
      claim.json             { lane, entry:{contract,function,args,value},
                               expected_divergence, declared_observable, ... }

Decision tree (halt at first terminal verdict):

  0. STRUCTURE CHECK           -> REJECT_MALFORMED on missing pieces
  1. REAL-BEHAVIOR CHECK       -> INVALID if the Forge test does not PASS
     1a. OVER_ACCEPT sub-case  -> solc must REJECT (skip Forge)
  2. REJECT GATE (§2)          -> REJECTED_OOS on any exclusion hit
  3. RUN SOLIDITY-LEAN + CLASSIFY:
     (a) fail-closed, solc ran -> COVERAGE_GAP (lane C)  [missing-feature/over-reject]
     (b) OVER_ACCEPT + solidity-lean runs solc-rejected prog -> SOUNDNESS_GAP (lane S)
     (c) solidity-lean runs, observable EQUAL   -> NO_DIVERGENCE
                          observable DIFFERS -> SOUNDNESS_GAP (lane S)
  + DEDUP (§6): terminal gaps get a root-cause fingerprint; a match against the
    known-open-gaps list => DUPLICATE annotation.

Qualifying verdicts (count for the leaderboard): COVERAGE_GAP (lane C),
SOUNDNESS_GAP (lane S). Everything else (INVALID, REJECTED_OOS, NO_DIVERGENCE,
REJECT_MALFORMED) does not qualify and returns the specific reason.

Qualifying submissions earn a place on the leaderboard.
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

from . import env as cenv
from . import exclusion_register as reg
from . import harness_bridge as hb
from . import known_gaps as kg
from . import measure as meas
from . import minimality as minim
from . import observable as obs
from . import reject_gate as gate


NAMESPACE_PREFIX = "SolidCore.Solidity.SolcAstImport.Contest"


# ---------------------------------------------------------------------------
# Verdict container
# ---------------------------------------------------------------------------

@dataclass
class Report:
    verdict: str
    lane: Optional[str] = None           # "C" | "S" | None
    reason: str = ""
    evidence: dict[str, Any] = field(default_factory=dict)
    fingerprint: Optional[dict[str, Any]] = None
    duplicate_of: Optional[str] = None
    register_version: str = reg.REGISTER_VERSION
    known_gaps_version: str = kg.KNOWN_GAPS_VERSION

    @property
    def qualifies(self) -> bool:
        """True if this verdict counts for the leaderboard (a real gap)."""
        return self.verdict in ("COVERAGE_GAP", "SOUNDNESS_GAP")

    def to_dict(self) -> dict[str, Any]:
        d: dict[str, Any] = {
            "verdict": self.verdict,
            "lane": self.lane,
            "reason": self.reason,
            "qualifies": self.qualifies,
            "register_version": self.register_version,
            "known_gaps_version": self.known_gaps_version,
            "evidence": self.evidence,
        }
        if self.fingerprint is not None:
            d["fingerprint"] = self.fingerprint
        if self.duplicate_of is not None:
            d["duplicate_of"] = self.duplicate_of
        return d


# ---------------------------------------------------------------------------
# Submission loading (step 0)
# ---------------------------------------------------------------------------

@dataclass
class Submission:
    root: Path
    claim: dict[str, Any]
    sources: list[Path]
    forge_root: Path


def load_submission(root: Path) -> tuple[Optional[Submission], Optional[Report]]:
    if not root.is_dir():
        return None, Report("REJECT_MALFORMED",
                            reason=f"submission dir not found: {root}")
    claim_path = root / "claim.json"
    if not claim_path.is_file():
        return None, Report("REJECT_MALFORMED", reason="missing claim.json")
    try:
        claim = json.loads(claim_path.read_text())
    except json.JSONDecodeError as exc:
        return None, Report("REJECT_MALFORMED", reason=f"claim.json invalid JSON: {exc}")
    # claim.json may parse to a non-object (a list / string / number). Every
    # downstream access is `claim.get(...)`, which would raise an UNCAUGHT
    # AttributeError and crash the adjudicator (audit finding: claim-field type
    # confusion). Require a JSON object.
    if not isinstance(claim, dict):
        return None, Report("REJECT_MALFORMED",
                            reason="claim.json must be a JSON object")

    src_dir = root / "src"
    sources = sorted(src_dir.glob("*.sol")) if src_dir.is_dir() else []
    if not sources:
        return None, Report("REJECT_MALFORMED", reason="no src/*.sol sources")

    if not (root / "test").is_dir() and claim.get("lane") != "S":
        # lane S OVER_ACCEPT may legitimately have no runnable test (solc rejects);
        # a single-file MANIFEST submission carries no submitter test at all (the
        # harness measures the EVM side itself from the declarative manifest).
        if not claim.get("_over_accept") and not claim.get("_manifest"):
            return None, Report("REJECT_MALFORMED", reason="missing test/ directory")

    for key in ("lane", "entry"):
        if key not in claim:
            return None, Report("REJECT_MALFORMED", reason=f"claim.json missing '{key}'")
    entry = claim["entry"]
    # `entry` must be a JSON object: a non-dict (int/str/list) makes the `key not
    # in entry` membership test below crash (TypeError on int) or pass spuriously
    # on a string substring match, and the later `entry.get(...)` in adjudicate()
    # raise an uncaught AttributeError (audit finding: claim-field type confusion).
    if not isinstance(entry, dict):
        return None, Report("REJECT_MALFORMED",
                            reason="claim.entry must be a JSON object")
    for key in ("contract", "function"):
        if key not in entry:
            return None, Report("REJECT_MALFORMED", reason=f"claim.entry missing '{key}'")
    if claim["lane"] not in ("C", "S"):
        return None, Report("REJECT_MALFORMED", reason="claim.lane must be 'C' or 'S'")

    return Submission(root=root, claim=claim, sources=sources, forge_root=root), None


# ---------------------------------------------------------------------------
# Fingerprint of a terminal verdict (§6.2)
# ---------------------------------------------------------------------------

def coverage_fingerprint(solidity_lean: hb.SolidityLeanResult) -> tuple:
    """lane C: (fail_stage, fail_reason_class, minimal_node_type_or_field)."""
    stage = solidity_lean.stage  # import | lean | run
    msg = solidity_lean.message
    if stage == "import":
        # classify the importer fail() reason (design §2)
        if "unimplemented" in msg:
            reason_class = "unimplemented"
        elif "unclassified" in msg:
            reason_class = "unclassified"
        elif "unknown" in msg:
            reason_class = "unknown_scalar"
        elif "excluded" in msg:
            reason_class = "excluded"  # register/importer drift bug (§2)
        else:
            reason_class = "import_fail"
        token = _first_token(msg)
        return (stage, reason_class, token)
    if stage == "run":
        return ("typecheck", "over_reject", _first_token(msg))
    return ("elaboration", "elab_reject", _first_token(msg))


def _is_executable_failure(msg: str) -> bool:
    """True if a Solidus reject message is the generic `executableFailure` wrapper
    (`TypeError.unsupported "checked executable ..."`, SolidCore Checked.lean:18).

    This wrapper is what `FunctionDef.call?` produces for EVERY fold-through
    `none`: out-of-fuel, non-termination, a runtime-unimplemented op, and a
    typecheck-during-exec reject all collapse to it, so it cannot be trusted as a
    clean missing-feature signal — it is routed to NEEDS_REVIEW."""
    return "checked executable" in (msg or "")


def _first_token(msg: str) -> str:
    """Extract a STABLE, collision-resistant node-type/field identity from a fail
    message (review D-2).

    Importer fail() messages have the shape
        "... nodes present: NodeA, NodeB"
        "... child fields present: Parent.field"
    Rather than take only the first word (which collides when two different gaps
    both bottom out in, say, `Mapping`, and is order-sensitive when solc lists
    several nodes), we collect ALL tokens after the last "present:", keep dotted
    field paths intact, dedupe and SORT them, and join — so the identity is
    deterministic and distinguishes distinct node/field sets."""
    if "present:" in msg:
        tail = msg.rsplit("present:", 1)[1]
        toks = [t.strip("() ") for t in tail.replace(",", " ").split()]
        toks = [t for t in toks if t and t.lower() not in ("and", "or")]
        if toks:
            return "+".join(sorted(set(toks)))
    for word in msg.replace(":", " ").replace(",", " ").split():
        if word[:1].isupper() and word.isalnum() and word not in ("Solidity", "AST"):
            return word
    return msg.strip().split(":")[0][:48] if msg else "unknown"


def soundness_fingerprint(comparison: obs.ObservableComparison,
                          feature: str) -> tuple:
    """lane S: (observable_component, minimal_feature, delta_shape)."""
    component = comparison.differing_component or "unknown"
    if component == "wrong-value":
        obs_component = "return_value"
    elif component in ("wrong-panic", "wrong-revert", "revert-vs-success"):
        obs_component = "revert_data"
    elif component in ("deploy-revert-vs-success", "deploy-vs-call-revert",
                       "wrong-deploy-revert"):
        # constructor-revert (deploy-phase) divergences: the engines disagree
        # on the deploy outcome or on the constructor's revert data.
        obs_component = "deploy_revert_data"
    else:
        obs_component = component
    return (obs_component, feature, component)


def _annotate_dedup(report: Report, lane: str, key: tuple, feature_token: str) -> None:
    report.fingerprint = {"lane": lane, "key": list(key),
                          "key_str": "|".join(str(k) for k in key)}
    hit = kg.match_fingerprint(lane, key) or kg.match_relaxed(lane, feature_token)
    if hit is not None:
        report.duplicate_of = hit.id
        report.reason += (f"  [DUPLICATE of known gap {hit.id}: {hit.feature}]")
    # ADVISORY delta-shape cluster hint (lane S). match_fingerprint/match_relaxed
    # both key on the SUBMITTER-CONTROLLED middle `feature` token, so a known gap
    # re-skinned with a novel feature dodges them and scores as novel (leaderboard
    # novelty-inflation, audit finding). This lists known-open gaps sharing the
    # ADJUDICATOR-derived (component, delta_shape) so a maintainer can catch the
    # re-skin. It NEVER sets duplicate_of (delta alone over-clusters distinct gaps,
    # e.g. G2..G12 all share `over_accept/over-accept`) and does NOT change
    # `qualifies` — a hint on the evidence only, biased to under-cluster.
    if lane == "S" and len(key) >= 3:
        cluster = [gid for gid in kg.cluster_by_delta(lane, key[0], key[2])
                   if gid != report.duplicate_of]
        if cluster:
            report.fingerprint["delta_cluster_hint"] = cluster


# ---------------------------------------------------------------------------
# The pipeline (steps 1-3)
# ---------------------------------------------------------------------------

def adjudicate(root: Path, tools: Optional[hb.ToolPaths] = None,
               work_dir: Optional[Path] = None, timeout: int = 400,
               skip_forge: bool = False,
               at_version: Optional[str] = None,
               env_override: Optional[cenv.EnvOverrides] = None,
               inject_storage: Optional[list[tuple[int, int]]] = None,
               _selftest_perturb_evm: Optional[Any] = None,
               _selftest_perturb_solidity_lean: Optional[Any] = None) -> Report:
    """Adjudicate a submission (design §4).

    ``at_version`` is the exclusion-register version in force at the submission's
    timestamp (§7 fairness invariant), used to select which exclusions apply. It
    is SERVER-AUTHORITATIVE (the portal sets it from the recorded submission
    time); ``None`` means the current register. The submitter's self-declared
    ``claim.register_version_seen`` is only cross-checked, never trusted to select
    the version — otherwise an adversary could claim an old version to dodge a
    newer exclusion (e.g. X-EXTCALL).

    ``_selftest_perturb_evm`` / ``_selftest_perturb_solidity_lean`` are TEST-ONLY seams
    (contest/run_samples.py): callables applied to the measured EVM observable /
    the real solidity-lean result to INJECT a synthetic divergence, so the
    divergence-DETECTION paths (SOUNDNESS_GAP / COVERAGE_GAP) can be exercised
    end-to-end over a real pipeline run WITHOUT leaving a bug in solidity-lean. Both
    MUST be None in real adjudication."""
    tools = tools or hb.ToolPaths()
    submission, malformed = load_submission(root)
    if malformed is not None:
        return malformed
    assert submission is not None
    claim = submission.claim
    entry = claim["entry"]
    lane = claim["lane"]
    over_accept = bool(claim.get("_over_accept") or
                       (lane == "S" and claim.get("mode") == "OVER_ACCEPT"))
    # Single-file MANIFEST mode: the submission carries no Forge test — the harness
    # measures the EVM side itself from the declarative manifest (deploy/entry/env/
    # storage). So the real-behavior INVALID gate (which runs the submitter's test)
    # is skipped; the independently MEASURED EVM run is authoritative by
    # construction, and the env comes from the manifest (env_override) rather than
    # from scanned test cheatcodes.
    manifest_mode = bool(claim.get("_manifest"))

    work = work_dir or Path(tempfile.mkdtemp(prefix="contest-adjudicate."))
    work.mkdir(parents=True, exist_ok=True)
    evidence: dict[str, Any] = {"submission": str(root), "lane_claimed": lane}

    # -- Step 0a: VALIDATE UNTRUSTED CLAIM FIELDS before any codegen ---------
    # Names reach generated Lean; fuel reaches the interpreter; args reach the
    # renderer. All are attacker-controlled (review findings 3/4/5).
    if not _valid_identifier(entry.get("contract")):
        return Report("REJECT_MALFORMED", reason=(
            f"entry.contract is not a valid identifier: {entry.get('contract')!r}"),
            evidence=evidence)
    if not _valid_identifier(entry.get("function")):
        return Report("REJECT_MALFORMED", reason=(
            f"entry.function is not a valid identifier: {entry.get('function')!r}"),
            evidence=evidence)
    fuel = _valid_fuel(claim.get("fuel", 64))
    if fuel is None:
        return Report("REJECT_MALFORMED", reason=(
            f"claim.fuel must be an integer in [1, {_FUEL_CAP}]"), evidence=evidence)
    args_lean, args_err = _safe_render_args(entry.get("args", []))
    if args_lean is None:
        return Report("REJECT_MALFORMED", reason=args_err or "bad args",
                      evidence=evidence)
    # Constructor args (optional): deployed to BOTH engines (measure.py appends
    # them to creationCode; solidity-lean passes them to constructWithContext). Same
    # untrusted arg forms as entry args, so validate them identically.
    ctor_args = entry.get("constructor_args", []) or []
    ctor_args_lean, ctor_err = _safe_render_args(ctor_args)
    if ctor_args_lean is None:
        return Report("REJECT_MALFORMED",
                      reason=f"constructor_args: {ctor_err or 'bad args'}",
                      evidence=evidence)
    slots, slots_err = _valid_slots(claim.get("observed_slots", []))
    if slots is None:
        return Report("REJECT_MALFORMED", reason=slots_err or "bad observed_slots",
                      evidence=evidence)

    # -- Step 0a': VALIDATE entry.args AGAINST the entry function SIGNATURE -----
    # The args reach the EVM as ABI calldata (decoded per the real parameter
    # types) AND Solidus as direct CoreValues. If they do not match the function's
    # parameter list the two engines receive DIFFERENT logical calls and diverge
    # for a NON-semantic reason. Critically, a wrong arg COUNT makes Solidus fail
    # closed on the call while the EVM still runs — which the classifier would
    # score as a bogus qualifying COVERAGE_GAP (a submitter could fabricate a
    # "gap" from a malformed call). So a signature mismatch is a MALFORMED claim,
    # never a gap. Skipped for OVER_ACCEPT (its program is solc-rejected and has
    # no runnable signature).
    entry_sig: Optional[meas.EntrySig] = None
    if not over_accept:
        try:
            entry_sig = meas.entry_signature(
                _src_for(submission.sources, entry["contract"], tools.solc)
                or submission.sources[0], entry["contract"], entry["function"],
                tools.solc)
        except OSError as exc:
            # missing/broken solc binary etc. — INFRA, not a malformed
            # submission (release audit: never terminally reject on a broken
            # toolchain).
            return Report("NEEDS_REVIEW", reason=(
                f"toolchain failure resolving the entry signature ({exc}); "
                "infra issue — retry, not evidence against the submission"),
                evidence=evidence)
        except Exception as exc:
            return Report("REJECT_MALFORMED", reason=(
                f"could not resolve entry signature: {exc}"), evidence=evidence)
        if entry_sig is None:
            return Report("REJECT_MALFORMED", reason=(
                f"entry {entry['contract']}.{entry['function']} not found / has "
                "no function selector in the compiled AST"), evidence=evidence)
        # OVERLOADED entry name (release audit): with two functions named
        # entry.function, the measurement encodes calldata for ONE overload
        # while the Lean by-name dispatch could resolve the OTHER — the engines
        # would receive different logical calls and diverge for a non-semantic
        # reason (a fabricatable divergence). v1 requires a uniquely-named
        # entry; rename the overloads to disambiguate.
        if entry_sig.overload_count > 1:
            return Report("REJECT_MALFORMED", reason=(
                f"entry {entry['contract']}.{entry['function']} is OVERLOADED "
                f"({entry_sig.overload_count} definitions share the name); the "
                "by-name entry is ambiguous across the two engines — give the "
                "entry function a unique name"), evidence=evidence)
        n_args, n_params = len(entry.get("args", [])), len(entry_sig.param_types)
        if n_args != n_params:
            return Report("REJECT_MALFORMED", reason=(
                f"entry.args count ({n_args}) does not match "
                f"{entry['contract']}.{entry['function']} parameter count "
                f"({n_params}): {entry_sig.param_types}"), evidence=evidence)
        # Array/struct/function PARAMETERS are outside what the v1 claim arg
        # forms can represent: a partial encoding would feed the engines
        # different logical calls. Out of scope — X-ARGVAL (register >= 1.3.0;
        # the retired broad X-RETABI covered this for older submissions).
        bad_params = [t for t in entry_sig.param_types
                      if not _representable_param_type(t)]
        oos_entry = _active_row(("X-ARGVAL", "X-RETABI"),
                                at_version or reg.REGISTER_VERSION)
        oos_active = oos_entry is not None
        if bad_params and oos_active:
            evidence["arg_type_scope"] = {"unsupported_params": bad_params}
            return Report("REJECTED_OOS", reason=(
                f"reject gate fired: {oos_entry.id} (intentional exclusion, out "
                f"of scope) — entry parameter type(s) {bad_params} not "
                f"representable by the v1 claim arg forms"), evidence=evidence)
        # Per-arg DOMAIN validation: each scalar arg must be a LEGAL value for its
        # parameter type. An out-of-domain value (dirty bool, out-of-range enum/
        # uintN/address) is not a legal high-level call — the EVM decoder reverts
        # while Solidus may accept or fail closed, fabricating a divergence for
        # essentially any contract with a scalar param. Reject as malformed; a
        # family we cannot bound from the type string ("__OOS__") is out of scope.
        enum_counts = meas.enum_member_counts(
            _src_for(submission.sources, entry["contract"], tools.solc)
            or submission.sources[0], tools.solc)
        for i, (arg, ptype) in enumerate(
                zip(entry.get("args", []), entry_sig.param_types)):
            derr = _arg_domain_error(arg, ptype, enum_counts)
            if derr == "__OOS__":
                if oos_active:
                    evidence["arg_type_scope"] = {"unvalidatable_param": ptype}
                    return Report("REJECTED_OOS", reason=(
                        f"reject gate fired: {oos_entry.id} (intentional "
                        f"exclusion, out of scope) — entry parameter type "
                        f"{ptype!r} (arg {i}) cannot be domain-validated from "
                        f"the v1 claim arg forms"), evidence=evidence)
                # No active row (unreachable while X-ARGVAL is live): fail safe
                # as malformed rather than letting an unvalidated arg through.
                return Report("REJECT_MALFORMED", reason=(
                    f"entry parameter type {ptype!r} (arg {i}) cannot be "
                    f"domain-validated from the v1 claim arg forms"),
                    evidence=evidence)
            elif derr is not None:
                return Report("REJECT_MALFORMED", reason=(
                    f"entry.args[{i}] is not a legal value for parameter "
                    f"{i} ({ptype}): {derr}"), evidence=evidence)
        # Constructor args are deployed to BOTH engines too, so validate their
        # count + domain against the constructor signature identically (same
        # fabrication surface as entry args).
        ctor_ptypes = meas.constructor_param_types(
            _src_for(submission.sources, entry["contract"], tools.solc)
            or submission.sources[0], entry["contract"], tools.solc)
        if len(ctor_args) != len(ctor_ptypes):
            return Report("REJECT_MALFORMED", reason=(
                f"constructor_args count ({len(ctor_args)}) does not match "
                f"{entry['contract']}'s constructor parameter count "
                f"({len(ctor_ptypes)}): {ctor_ptypes}"), evidence=evidence)
        for i, (arg, ptype) in enumerate(zip(ctor_args, ctor_ptypes)):
            derr = _arg_domain_error(arg, ptype, enum_counts)
            if derr == "__OOS__":
                if oos_active:
                    evidence["arg_type_scope"] = {"unvalidatable_ctor_param": ptype}
                    return Report("REJECTED_OOS", reason=(
                        f"reject gate fired: {oos_entry.id} (intentional "
                        f"exclusion, out of scope) — constructor parameter type "
                        f"{ptype!r} (arg {i}) cannot be domain-validated from "
                        f"the v1 claim arg forms"), evidence=evidence)
                return Report("REJECT_MALFORMED", reason=(
                    f"constructor parameter type {ptype!r} (arg {i}) cannot be "
                    f"domain-validated from the v1 claim arg forms"),
                    evidence=evidence)
            elif derr is not None:
                return Report("REJECT_MALFORMED", reason=(
                    f"constructor_args[{i}] is not a legal value for constructor "
                    f"parameter {i} ({ptype}): {derr}"), evidence=evidence)

    # -- Step 0b: CHEATCODE GATE over BOTH src AND test, BEFORE any Forge run.
    # The trust boundary is any call to the cheatcode ADDRESS from any submitted
    # code executed under `forge test` (adversarial-review findings 1 & 2). We
    # scan src too, because measure.py DEPLOYS and calls the entry contract — a
    # cheatcode call from the entry contract forges the measured EVM observable.
    # This MUST run before Forge/measurement so untrusted code never executes
    # with a cheatcode reference the gate would have caught.
    env_ov = cenv.EnvOverrides()
    # entry.value is attacker-controlled and reaches BOTH the Foundry measurement
    # (call{value:...}) and the Solidus env. A non-numeric value used to raise an
    # UNCAUGHT ValueError (adjudicator crash); a negative / >uint256 value is not a
    # legal msg.value. Validate it as an integer in [0, 2^256) -> REJECT_MALFORMED.
    val = _valid_value(entry.get("value", 0))
    if val is None:
        return Report("REJECT_MALFORMED", reason=(
            "entry.value must be an integer in [0, 2**256)"), evidence=evidence)
    env_ov.value = val
    try:
        src_asts = gate.get_source_asts(submission.sources, tools.solc)
    except OSError as exc:
        # missing/broken solc binary etc. — INFRA (release audit): route to
        # review instead of a terminal reject.
        return Report("NEEDS_REVIEW", reason=(
            f"toolchain failure running solc on the sources ({exc}); infra "
            "issue — retry, not evidence against the submission"),
            evidence=evidence)
    except Exception as exc:  # solc failure on adversarial source (finding 5)
        if over_accept:
            # An OVER_ACCEPT program is solc-rejected BY DEFINITION, so the
            # analyzed-AST path always fails here — rejecting made the whole
            # over-accept lane dead code (the lane check below never ran).
            # Parse-only ASTs carry every syntax node the scans traverse.
            try:
                src_asts = gate.get_source_asts_parse_only(
                    submission.sources, tools.solc)
            except Exception as exc2:
                return Report("REJECT_MALFORMED", reason=(
                    f"OVER_ACCEPT source does not even parse under pinned "
                    f"solc: {exc2}"), evidence=evidence)
        else:
            return Report("REJECT_MALFORMED", reason=(
                f"solc could not analyze the submitted sources: {exc}"),
                evidence=evidence)
    test_asts = _test_asts(submission.root, tools.solc)
    src_scan = gate.scan_src_cheatcodes(src_asts)
    test_scan = gate.scan_test_cheatcodes(test_asts)
    evidence["cheatcodes"] = {
        "src_banned": [h.to_dict() for h in src_scan.banned],
        "test_banned": [h.to_dict() for h in test_scan.banned],
        "unmirrorable": [h.to_dict() for h in
                         (src_scan.unmirrorable + test_scan.unmirrorable)],
        "overrides": test_scan.overrides.to_dict(),
    }
    banned = src_scan.banned + test_scan.banned
    if banned:
        ids = ", ".join(sorted({h.id for h in banned}))
        where = "src" if src_scan.banned else "test"
        return Report("REJECTED_OOS", reason=(
            f"submission {where} references the cheatcode address / uses a "
            f"banned cheatcode ({ids}); state/oracle-forging cheatcodes are not "
            "allowed (default-deny)"), evidence=evidence)
    if test_scan.unmirrorable:
        return Report("REJECTED_OOS", reason=(
            "test uses a whitelisted cheatcode with a non-literal argument that "
            "cannot be mirrored into the solidity-lean env (v1 requires literals)"),
            evidence=evidence)
    if manifest_mode and env_override is not None:
        # Manifest mode: the env is the declarative manifest `env` block (already
        # mirrored into both engines), NOT scanned test cheatcodes. Preserve the
        # validated entry.value.
        env_override.value = env_ov.value
        env_ov = env_override
    else:
        # merge the mirrored overrides, preserving the entry value.
        test_scan.overrides.value = env_ov.value
        env_ov = test_scan.overrides

    # -- Step 1 / 1a: REAL-BEHAVIOR CHECK ------------------------------------
    measured: Optional[meas.Measurement] = None
    structs: dict[str, list[str]] = {}  # struct canonical name -> member types
    if over_accept:
        # error_code pins the reject to a semantic cause (review L-1 / P1).
        code = claim.get("solc_error_code") or claim.get("solc_reject_error_code")
        ok, status = hb.run_solc_rejects_source(
            submission.sources[0], work / "solc-rejects", error_code=code,
            tools=tools, timeout=timeout)
        evidence["solc_rejects"] = status
        if not ok:
            # An INFRA-shaped failure (timeout) is not evidence the claim is
            # false — route to review, never a terminal INVALID (release
            # audit: fail-closed-to-terminal silently invalidated valid
            # submissions when the toolchain hiccuped).
            if status.startswith("timeout"):
                return Report("NEEDS_REVIEW", reason=(
                    f"solc reject-check failed inconclusively ({status}); "
                    "cannot conclude the OVER_ACCEPT claim is false"),
                    evidence=evidence)
            return Report("INVALID", reason=(
                "OVER_ACCEPT claim but pinned solc did NOT reject the program "
                f"as declared ({status})"), evidence=evidence)
    elif not skip_forge:
        # A submitter Forge test is the real-behavior INVALID gate. Manifest mode
        # has no submitter test — the MEASURED EVM run below is authoritative by
        # construction — so this gate runs only for the legacy dir format.
        if not manifest_mode:
            mc = claim.get("forge_match_contract")
            mt = claim.get("forge_match_test")
            ok, status = hb.run_forge_test(
                submission.forge_root, work / "forge", match_contract=mc,
                match_test=mt, tools=tools, timeout=timeout)
            evidence["forge"] = status
            if not ok:
                # INFRA-shaped failures (timeout / missing tool / OS error) are
                # not evidence the claimed behavior fails to reproduce: route
                # to review instead of a terminal INVALID (release audit —
                # fairness: a broken toolchain must never silently invalidate
                # a valid submission). A genuine test failure (forge ran, the
                # submitter's test FAILED: forge_exit_N) stays INVALID.
                if status.startswith(("timeout", "infra_error")):
                    return Report("NEEDS_REVIEW", reason=(
                        "the real-behavior Forge run failed inconclusively "
                        f"({status[:200]}); retry after fixing the "
                        "toolchain/timeout — not evidence against the claim"),
                        evidence=evidence)
                return Report("INVALID", reason=(
                    "claimed behavior does not reproduce on pinned solc 0.8.35 + "
                    f"Foundry (forge={status})"), evidence=evidence)
        # -- MEASURE the EVM observable from an actual Forge run (P0 #1) -----
        # Reuse the signature resolved + validated in step 0a' (recompute only if
        # that path was skipped, e.g. a future caller that bypasses it).
        sig = entry_sig or meas.entry_signature(
            _src_for(submission.sources, entry["contract"], tools.solc)
            or submission.sources[0], entry["contract"], entry["function"],
            tools.solc)
        if sig is None:
            return Report("REJECT_MALFORMED", reason=(
                f"entry {entry['contract']}.{entry['function']} not found / has "
                "no function selector in the compiled AST"), evidence=evidence)
        # Scope check (return channel): register >= 1.3.0 decodes ARRAYS and
        # STRUCTS (arbitrarily nested) into solidity-lean's [..]/(..) rendering,
        # so they are MEASURED + COMPARED, not excluded. The residue is X-FNVAL:
        # a function-typed value (or an unresolvable struct) anywhere in the
        # return types still renders asymmetrically. For submissions judged at a
        # pre-1.3.0 register the broad X-RETABI subset applies unchanged (§7).
        structs = meas.struct_definitions(sig.source_file, tools.solc)
        legacy_retabi = reg.entry_by_id("X-RETABI")
        if legacy_retabi is not None and \
                legacy_retabi.is_active(at_version or reg.REGISTER_VERSION):
            uncomparable = [t for t in sig.return_types
                            if not _representable_param_type(t)]
            if uncomparable:
                evidence["return_type_scope"] = {"uncomparable": uncomparable}
                return Report("REJECTED_OOS", reason=(
                    f"reject gate fired: X-RETABI (intentional exclusion, out of "
                    f"scope) — entry return type(s) {uncomparable} not in the "
                    f"faithfully-comparable ABI subset"), evidence=evidence)
        else:
            uncomparable = [t for t in sig.return_types
                            if not _comparable_channel_type(t, structs)]
            if uncomparable:
                e = reg.entry_by_id("X-FNVAL")
                if e is not None and e.is_active(at_version or reg.REGISTER_VERSION):
                    evidence["return_type_scope"] = {"uncomparable": uncomparable}
                    return Report("REJECTED_OOS", reason=(
                        f"reject gate fired: X-FNVAL (intentional exclusion, out "
                        f"of scope) — entry return type(s) {uncomparable} carry a "
                        f"function-typed / unresolvable value outside the "
                        f"faithfully-comparable ABI subset"), evidence=evidence)
        measured, mstatus = meas.measure_evm(
            sig, entry.get("args", []), env_ov, work / "measure",
            forge=tools.forge, solc=tools.solc, repo=tools.repo, timeout=timeout,
            slots=slots, constructor_args=ctor_args,
            inject_storage=inject_storage)
        evidence["evm_measurement"] = (measured.raw if measured else mstatus)
        if measured is not None and measured.deploy_reverted:
            # A CONSTRUCTOR revert is a first-class measured outcome (the
            # harness captures the deploy's revert data instead of aborting);
            # it is compared against the model's own constructor outcome below.
            evidence["deploy_reverted"] = True
        if measured is None:
            # The measurement harness is MAINTAINER-generated: by this point the
            # submission already passed structure/arg validation, the cheatcode
            # gate, and (non-manifest) its OWN forge test. A failure to produce
            # the measured observable is therefore a genuine infra/harness
            # issue, not evidence against the claim — route to review, never a
            # terminal INVALID (release audit fairness fix; the old terminal
            # reject silently invalidated valid submissions on toolchain
            # hiccups or OOM). Note a CONSTRUCTOR revert is NOT such a failure:
            # the harness measures it as a `deployrevert|...` observable.
            return Report("NEEDS_REVIEW", reason=(
                f"could not measure the EVM observable from the Forge run "
                f"({mstatus[:300]}); measurement infra/harness failure — "
                "needs maintainer retry/review, not a terminal reject"),
                evidence=evidence)
        # Mirror the deployed entry address into the solidity-lean env so
        # address(this) agrees by construction (review E-1).
        env_ov.self_addr = measured.self_addr
    else:
        evidence["forge"] = "skipped"

    # -- Step 2: REJECT GATE (whole submission) ------------------------------
    # Judge against the register in force at submission time (§7). at_version is
    # server-authoritative; the claim's register_version_seen is only cross-checked.
    effective_version = at_version or reg.REGISTER_VERSION
    seen = claim.get("register_version_seen")
    if seen and str(seen) != effective_version:
        evidence["register_version_note"] = {
            "declared_seen": seen, "adjudicated_at": effective_version,
            "note": "adjudication uses the register in force at submission time "
                    "(server-authoritative), not the claim's declared version."}
    gate_verdict = gate.run_gate(submission.sources, solc=tools.solc,
                                 enforce_v1_multi=True, at_version=effective_version,
                                 parse_only_fallback=over_accept)
    evidence["gate"] = gate_verdict.to_dict()
    if not gate_verdict.is_pass:
        ids = ", ".join(sorted({h.id for h in gate_verdict.hits}))
        return Report("REJECTED_OOS", reason=(
            f"reject gate fired: {ids} (intentional exclusion, out of scope)"),
            evidence=evidence)

    # Minimality / shrink advisory (§6.3): flag dead code / haystack. Advisory
    # only — annotates evidence, never changes the verdict.
    evidence["minimality"] = minim.minimality_report(
        submission.sources, entry["contract"], entry["function"], tools.solc)

    # -- Step 3: RUN SOLIDITY-LEAN -------------------------------------------------
    # (v1 single-contract: the responder-free ownCall path.)
    src = _source_of_contract(submission.sources, entry["contract"], tools.solc)
    if src is None:
        return Report("REJECT_MALFORMED", reason=(
            f"entry contract {entry['contract']!r} not found in submitted sources"),
            evidence=evidence)
    namespace = f"{NAMESPACE_PREFIX}.{_sanitize(root.name)}"
    # The interpreter runs at _FUEL_CAP, NOT at the submitter's `fuel` (audit
    # finding, CONTEST-BREAKING). Statement-fuel exhaustion renders as a clean
    # `solidity-lean-reject` (`.error .outOfFuel` folds through FunctionDef.call?
    # into the generic `executableFailure` wrapper, indistinguishable from a real
    # reject) which the classifier would otherwise bank as a qualifying
    # COVERAGE_GAP. A submitter picking `fuel: 1` could thus fabricate a gap on
    # nearly any program. Running at the cap removes cheap starvation; the
    # residual (a program that genuinely needs > cap, e.g. an infinite loop) is
    # handled below by routing run-stage `executableFailure` rejects — which are
    # provably indistinguishable from out-of-fuel/non-termination — to
    # NEEDS_REVIEW rather than auto-qualifying. `fuel` is still validated (bad
    # values -> REJECT_MALFORMED) but no longer drives the interpreter down.
    # The entry call's REAL ABI calldata (selector ++ encoded args) — identical
    # bytes to what the Foundry measurement sends — is mirrored into the Lean
    # entry context so msg.data/msg.sig observables are faithful (d206: the
    # by-name entry ran with empty calldata, making every msg.data probe a
    # spurious "divergence"). No sig for OVER_ACCEPT (solc-rejected): those
    # keep the default empty calldata, matching a program that never runs.
    lean_calldata: Optional[str] = None
    if entry_sig is not None:
        try:
            lean_calldata = meas.build_calldata(
                entry_sig.selector, entry.get("args", []))
        except Exception:
            lean_calldata = None  # unencodable args were already rejected above
    solidity_lean = hb.run_solidity_lean_observable(
        src, entry["contract"], entry["function"], entry.get("args", []),
        work / "solidity_lean", namespace, fuel=_FUEL_CAP,
        tools=tools, timeout=timeout, env=env_ov, slots=slots,
        constructor_args=ctor_args, inject_storage=inject_storage,
        calldata_hex=lean_calldata)
    if _selftest_perturb_solidity_lean is not None:  # coverage bug-injection self-test
        solidity_lean = _selftest_perturb_solidity_lean(solidity_lean)
        evidence["selftest_solidity_lean_perturbed"] = True
    evidence["env"] = env_ov.to_dict()
    evidence["solidity_lean"] = {
        "ok": solidity_lean.ok, "stage": solidity_lean.stage,
        "fail_closed": solidity_lean.fail_closed, "message": solidity_lean.message[:1000],
        "observable": solidity_lean.observable.raw if solidity_lean.observable else None,
    }

    # (3b) OVER_ACCEPT: solidity-lean ran a program solc rejected -> lane S.
    if over_accept:
        if solidity_lean.ok:
            report = Report("SOUNDNESS_GAP", lane="S", reason=(
                "solidity-lean imports+typechecks+runs a program that pinned solc "
                "REJECTS (over-accept)"), evidence=evidence)
            key = ("over_accept", claim.get("feature", "over-accept"), "over-accept")
            _annotate_dedup(report, "S", key, claim.get("feature", "over-accept"))
            return report
        # solidity-lean also rejected: agrees with solc -> not a gap.
        return Report("NO_DIVERGENCE", reason=(
            "both pinned solc and solidity-lean reject the program (agree)"),
            evidence=evidence)

    # (3a) solidity-lean FAILS CLOSED while solc accepted+ran -> lane C coverage gap.
    if solidity_lean.fail_closed:
        # An INCONCLUSIVE failure (timeout / resource exhaustion / harness crash /
        # build or toolchain/environment error, incl. a poisoned fuel) is NOT
        # evidence of a missing feature (review finding 3). Never auto-qualify it;
        # route to maintainer review.
        if solidity_lean.inconclusive:
            return Report("NEEDS_REVIEW", reason=(
                "solidity-lean run failed inconclusively (timeout / resource "
                "exhaustion / build or environment error), not a clean reject: "
                f"{solidity_lean.message[:300]}"),
                evidence=evidence)
        # A RUN-stage fail-closed carrying the generic `executableFailure` wrapper
        # ("checked executable ...") is AMBIGUOUS and must NOT auto-qualify (audit
        # finding, CONTEST-BREAKING). `FunctionDef.call?` folds statement-fuel
        # exhaustion (`.error .outOfFuel`), non-termination (an infinite loop that
        # exhausts even _FUEL_CAP), a runtime-unimplemented operation, AND a
        # typecheck-during-exec reject into the SAME `none` -> the SAME
        # `TypeError.unsupported "checked executable ..."` string (SolidCore
        # Checked.lean:18). They are provably indistinguishable at this layer, so
        # a submitter could mint a COVERAGE_GAP with an infinite loop (the EVM
        # just reverts out-of-gas). Route these to human review; a genuine
        # missing-feature reject surfaces distinctly at the IMPORT stage (an
        # unsupported NODE) and still auto-qualifies below.
        if solidity_lean.stage == "run" and _is_executable_failure(solidity_lean.message):
            return Report("NEEDS_REVIEW", reason=(
                "solidity-lean fails closed at run stage with the generic "
                "executable-failure wrapper, which is indistinguishable from "
                "out-of-fuel / non-termination / a runtime-unimplemented op; a "
                "human must confirm this is a genuine coverage gap and not fuel "
                f"exhaustion: {solidity_lean.message[:300]}"),
                evidence=evidence)
        finger = coverage_fingerprint(solidity_lean)
        if finger[1] == "excluded":
            return Report("REJECTED_OOS", reason=(
                "importer reports an EXCLUDED node the gate did not catch "
                "(register/importer drift - gate bug, §2), not a coverage gap"),
                evidence=evidence)
        # Sub-kind follows the importer/typecheck REASON CLASS, not the stage
        # (review D-1): a type/elaboration reject of a solc-accepted program is
        # an over-reject; unimplemented/unclassified/unknown is a missing feature.
        reason_class = finger[1]
        sub_kind = ("over_reject" if reason_class in ("over_reject", "typecheck_reject")
                    else "missing_feature")
        evidence["coverage_reason_class"] = reason_class
        report = Report("COVERAGE_GAP", lane="C", reason=(
            f"solidity-lean fails closed ({solidity_lean.stage}: {sub_kind}, "
            f"{reason_class}) on an in-scope, solc-accepted program"),
            evidence=evidence)
        _annotate_dedup(report, "C", finger, finger[2])
        return report

    # (3c) solidity-lean ran to completion -> compare against the MEASURED EVM
    # observable (review P0 #1: the oracle is the Forge run, NOT the claim).
    if measured is None:
        return Report("REJECT_MALFORMED", reason=(
            "no measured EVM observable available (Forge measurement did not "
            "run); cannot adjudicate a soundness claim without the oracle"),
            evidence=evidence)
    # Custom-error definitions (name + params + selector) from the entry source,
    # so a custom-error revert decodes to custom:<Name>:... instead of raw:.
    error_defs, ambiguous_sels = meas.error_definitions(sig.source_file, tools.solc)
    evidence["custom_errors"] = {sel: name for sel, (name, _t) in error_defs.items()}
    if ambiguous_sels:
        evidence["ambiguous_error_selectors"] = sorted(ambiguous_sels)
    if not measured.ok:
        _rd = bytes.fromhex(measured.ret_hex[2:]
                            if measured.ret_hex.startswith("0x")
                            else measured.ret_hex)
        _sel = _rd[:4].hex() if len(_rd) >= 4 else ""
        # AMBIGUOUS revert selector (a 4-byte collision between two-or-more
        # distinctly-named custom errors; solc 0.8.35 rejects colliding errors
        # within one contract but ACCEPTS a file-level/cross-contract collision,
        # so such programs are legal). The EVM dispatches revert data by BYTES
        # (selector+args) — the error NAME is not on-chain-observable. Register
        # >= 1.3.0 therefore resolves the colliding selector to the error the
        # MODEL reports (when its full selector matches the measured one) and
        # compares the byte-faithful decoded form:
        #   * model+EVM bytes agree  -> both sides render the same name+args ->
        #     NO_DIVERGENCE (a planted collision cannot FABRICATE a gap);
        #   * bytes differ           -> the decoded forms differ -> a genuine
        #     divergence is still banked (resolution cannot MASK one, since the
        #     label choice never alters the decoded arg values, only whose
        #     declared param types the same bytes are decoded under — the
        #     model's own claim, i.e. exactly "does the model's revert encode
        #     to the measured bytes").
        # Pre-1.3.0 submissions keep the historical X-ERRSEL OOS routing (§7).
        if _sel and _sel in ambiguous_sels:
            _e = reg.entry_by_id("X-ERRSEL")
            if _e is not None and _e.is_active(effective_version):
                evidence["ambiguous_revert_selector"] = _sel
                return Report("REJECTED_OOS", reason=(
                    f"reject gate fired: X-ERRSEL (intentional exclusion, out of "
                    f"scope) — the revert selector 0x{_sel} is defined by two or "
                    f"more distinctly-named custom errors (a 4-byte selector "
                    f"collision); the on-chain revert is indistinguishable between "
                    f"them, so the custom-error name is not a faithful observable"),
                    evidence=evidence)
            model_name = _model_custom_error_name(
                solidity_lean.observable.raw if solidity_lean.observable else "")
            resolved = None
            if model_name:
                for _s2, _n2, _t2 in meas.error_definition_list(
                        sig.source_file, tools.solc):
                    if _s2 == _sel and _n2 == model_name:
                        resolved = (_n2, _t2)
                        break
            if resolved is not None:
                error_defs[_sel] = resolved
            evidence["ambiguous_revert_selector"] = {
                "selector": _sel,
                "resolved_to": resolved[0] if resolved else error_defs[_sel][0],
                "note": "colliding 4-byte selector resolved to the model-reported "
                        "error; the name is not on-chain-observable, comparison "
                        "is on the byte-faithful selector+args form."}
        # Scope check (revert channel): with the recursive codec, array/struct
        # error params decode into the exact [..]/(..) form solidity-lean renders
        # and ARE compared. The residue is X-FNVAL (function-typed / unresolvable
        # value); pre-1.3.0 submissions keep the broad X-RETABI subset (§7).
        if _sel in error_defs:
            _ename, _etypes = error_defs[_sel]
            _legacy = reg.entry_by_id("X-RETABI")
            if _legacy is not None and _legacy.is_active(effective_version):
                _uncomparable = [t for t in _etypes
                                 if not _representable_param_type(t)]
                if _uncomparable:
                    evidence["revert_param_scope"] = {
                        "error": _ename, "uncomparable": _uncomparable}
                    return Report("REJECTED_OOS", reason=(
                        f"reject gate fired: X-RETABI (intentional exclusion, out of "
                        f"scope) — custom-error {_ename} param type(s) "
                        f"{_uncomparable} not in the faithfully-comparable ABI "
                        f"subset (revert channel)"), evidence=evidence)
            else:
                _uncomparable = [t for t in _etypes
                                 if not _comparable_channel_type(t, structs)]
                _e = reg.entry_by_id("X-FNVAL")
                if _uncomparable and _e is not None and \
                        _e.is_active(effective_version):
                    evidence["revert_param_scope"] = {
                        "error": _ename, "uncomparable": _uncomparable}
                    return Report("REJECTED_OOS", reason=(
                        f"reject gate fired: X-FNVAL (intentional exclusion, out of "
                        f"scope) — custom-error {_ename} param type(s) "
                        f"{_uncomparable} carry a function-typed / unresolvable "
                        f"value outside the faithfully-comparable ABI subset "
                        f"(revert channel)"), evidence=evidence)
    try:
        evm_obs = obs.evm_observable(
            measured.ok, measured.ret_hex, sig.return_types,
            events=measured.events, storage=measured.storage, errors=error_defs,
            deploy_reverted=measured.deploy_reverted, structs=structs)
    except ValueError as exc:
        # The recursive ABI decoder found the measured bytes inconsistent with
        # the declared types. High-level solc-compiled code always emits
        # well-formed encodings (assembly is excluded), so this is an infra/
        # harness anomaly — route to review, never auto-classify (it must not
        # be a fabrication vector for either side).
        return Report("NEEDS_REVIEW", reason=(
            f"could not decode the measured EVM return/revert data against the "
            f"declared ABI types ({exc}); measurement/decoder anomaly — needs "
            "maintainer review"), evidence=evidence)
    if _selftest_perturb_evm is not None:  # fault-injection self-test only
        evm_obs = _selftest_perturb_evm(evm_obs)
        evidence["selftest_perturbed"] = True
    evidence["evm_observable"] = evm_obs.to_dict()
    # declared_observable is now only a sanity cross-check (misreport hint).
    declared_norm = (claim.get("declared_observable", {}) or {}).get("normal_form")
    if declared_norm and declared_norm.strip() != evm_obs.raw.strip():
        evidence["declared_mismatch"] = {
            "declared": declared_norm, "measured": evm_obs.raw,
            "note": "submitter's declared_observable disagrees with the measured "
                    "EVM observable; adjudication uses the MEASURED value."}
    assert solidity_lean.observable is not None
    # Canonicalize a `revert|raw:0x..` outcome on EITHER side by re-decoding the
    # bytes through the same selector decoder: solidity-lean renders a dynamically
    # built string revert as raw bytes while the EVM side always decodes, so the
    # SAME revert data compared unequal (raw:0x08c379a0.. vs error:..) and banked a
    # fabricated wrong-revert SOUNDNESS_GAP. Symmetric; real byte differences still
    # decode to different forms, so genuine divergences are preserved.
    sl_obs = obs.canonicalize_raw_revert(solidity_lean.observable, error_defs,
                                         structs=structs)
    evm_cmp = obs.canonicalize_raw_revert(evm_obs, error_defs, structs=structs)
    comparison = obs.compare_observables(sl_obs, evm_cmp)
    evidence["comparison"] = comparison.to_dict()

    if comparison.equal:
        return Report("NO_DIVERGENCE", reason=(
            "solidity-lean observable equals the solc+EVM observable (agree)"),
            evidence=evidence)

    feature = claim.get("feature", "unspecified-feature")
    report = Report("SOUNDNESS_GAP", lane="S", reason=(
        f"solidity-lean runs but the observable DIFFERS "
        f"({comparison.differing_component}): solidity_lean={solidity_lean.observable.raw} "
        f"vs solc+EVM={evm_obs.raw}"), evidence=evidence)
    key = soundness_fingerprint(comparison, feature)
    _annotate_dedup(report, "S", key, feature)
    return report


def _sanitize(name: str) -> str:
    return "".join(c if c.isalnum() else "_" for c in name).strip("_") or "Sub"


import re as _re

_IDENT_RE = _re.compile(r"^[A-Za-z_$][A-Za-z0-9_$]*$")


def _valid_identifier(name: object) -> bool:
    """A Solidity identifier — enforced on entry.contract / entry.function in
    ALL paths BEFORE either name is interpolated into generated Lean (review
    finding 4: an unchecked name could close the Lean string literal and inject
    code)."""
    return isinstance(name, str) and bool(_IDENT_RE.match(name))


def _representable_param_type(t: str) -> bool:
    """True iff a PARAMETER type is representable by the v1 claim arg forms
    (word / {int} / {bytes} / bool) — the X-ARGVAL fence (and the historical
    X-RETABI subset for pre-1.3.0 submissions, which applied the same shape rule
    to return types as well). Arrays, structs, tuples, and function types have
    no arg form; a partial encoding would feed the two engines different logical
    calls and fabricate a divergence."""
    t = str(t).strip()
    for suffix in (" memory", " calldata", " storage", " payable"):
        t = t.replace(suffix, "")
    t = t.strip()
    if t.endswith("]"):            # any array — dynamic T[] or fixed T[N]
        return False
    if t.startswith("struct "):    # struct (no arg form)
        return False
    if t.startswith("tuple"):      # explicit tuple type
        return False
    if t.startswith("function"):   # function pointer (no arg form)
        return False
    return True


def _comparable_channel_type(t: str,
                             structs: Optional[dict[str, list[str]]]) -> bool:
    """True iff a RETURN / custom-error REVERT type is in the faithfully-
    comparable ABI subset under the recursive codec (register >= 1.3.0).

    The recursive decoder (observable._decode_abi_values) renders scalars,
    dynamic bytes/string, arrays (``[..]``) and structs (``(..)``) exactly as
    solidity-lean does, so all of those COMPARE. The residue (X-FNVAL) is a
    FUNCTION-typed value anywhere in the type — solidity-lean renders it via the
    r:reprStr fallback while the EVM ABI-encodes a static word — and a struct
    the harness cannot resolve to member types (undecodable)."""
    t = str(t).strip()
    for suffix in (" memory", " calldata", " storage", " payable"):
        t = t.replace(suffix, "")
    t = t.strip()
    if t.startswith("function"):
        return False
    arr = obs._array_elem(t)
    if arr is not None:
        return _comparable_channel_type(arr[0], structs)
    members = obs._struct_member_types(t, structs)
    if members is not None:
        return all(_comparable_channel_type(m, structs) for m in members)
    if t.startswith("struct "):    # unresolvable struct -> undecodable
        return False
    if t.startswith("tuple"):      # bare tuple typeString (no component info)
        return False
    if t.startswith("mapping"):    # not ABI-encodable anyway; fail safe
        return False
    return True


def _active_row(ids: tuple[str, ...],
                at_version: Optional[str]) -> Optional[reg.ExclusionEntry]:
    """The FIRST register row among ``ids`` active at ``at_version`` (used to
    pick the narrow 1.3.0 row for current submissions and the retired broad row
    for historical ones, §7)."""
    for entry_id in ids:
        e = reg.entry_by_id(entry_id)
        if e is not None and e.is_active(at_version):
            return e
    return None


def _model_custom_error_name(raw_observable: str) -> Optional[str]:
    """The custom-error NAME the model reports in its normal-form observable
    (``revert|custom:<Name>:...`` or ``deployrevert|custom:<Name>:...``), used
    to resolve an ambiguous (colliding) measured revert selector. None when the
    model's outcome is not a custom-error revert."""
    line = raw_observable.split("##EVT##", 1)[0].strip()
    for head in ("revert|custom:", "deployrevert|custom:"):
        if line.startswith(head):
            rest = line[len(head):]
            name = rest.split(":", 1)[0]
            return name or None
    return None


def _arg_as_word(arg: object) -> Optional[int]:
    """The unsigned word value an arg denotes, or None if the form is not
    word-family (a signed {int} or a {bytes} is not a plain word)."""
    if isinstance(arg, bool):
        return 1 if arg else 0
    if isinstance(arg, int):
        return arg if arg >= 0 else None
    if isinstance(arg, dict) and "word" in arg:
        try:
            w = int(arg["word"])
        except (TypeError, ValueError):
            return None
        return w if w >= 0 else None
    return None


def _arg_as_signed(arg: object) -> Optional[int]:
    """The signed value an arg denotes for an intN parameter, or None."""
    if isinstance(arg, bool):
        return None
    if isinstance(arg, int):
        return arg
    if isinstance(arg, dict):
        if "int" in arg:
            try:
                return int(arg["int"])
            except (TypeError, ValueError):
                return None
        if "word" in arg:
            try:
                w = int(arg["word"])
            except (TypeError, ValueError):
                return None
            return w if w >= 0 else None
    return None


def _clean_param_type(t: str) -> str:
    t = str(t).strip()
    for suffix in (" memory", " calldata", " storage", " payable"):
        t = t.replace(suffix, "")
    return t.strip()


def _arg_domain_error(arg: object, ptype: str,
                      enum_counts: dict[str, int]) -> Optional[str]:
    """Validate that ``arg`` is a LEGAL high-level value for parameter type
    ``ptype``; return an error string if not (else None).

    The args reach Solidus as typed CoreValues and the EVM as ABI calldata, whose
    external decoder REVERTS on out-of-domain scalars (dirty bool, out-of-range
    enum/uintN/address, non-zero padding). An out-of-domain arg is therefore not a
    legal call and would fabricate a divergence, so it is rejected as malformed.
    Returns the sentinel ``"__OOS__"`` for a scalar family we cannot validate
    from the type string (the caller maps that to an X-ARGVAL exclusion — the
    retired broad X-RETABI for pre-1.3.0 submissions)."""
    # A bare JSON integer denotes the UNSIGNED word form (render_lean_arg maps it
    # to `Value.word n`, which requires a Nat). A bare NEGATIVE integer is thus an
    # ill-formed word: measure._encode_arg two's-complements it (0xff..fb) while the
    # Lean renderer emits `Value.word -5` and FAILS TO ELABORATE (exit 1 -> a
    # NEEDS_REVIEW that burns human review), an encode/render asymmetry. Signed
    # values MUST use the explicit {"int": n} form. Reject uniformly, pre-dispatch.
    if isinstance(arg, int) and not isinstance(arg, bool) and arg < 0:
        return (f"a bare negative integer ({arg}) is ambiguous (the plain-int form "
                f"is the unsigned word form); use the {{\"int\": {arg}}} form for "
                f"signed values")
    t = _clean_param_type(ptype)
    # dynamic bytes/string: must be the {bytes} form
    if t in ("bytes", "string"):
        if isinstance(arg, dict) and "bytes" in arg:
            return None
        return f"{t} parameter requires a {{\"bytes\": \"0x..\"}} arg, got {arg!r}"
    if t == "bool":
        w = _arg_as_word(arg)
        if w in (0, 1):
            return None
        return f"bool parameter requires 0/1 or true/false, got {arg!r}"
    import re as _rex
    m = _rex.fullmatch(r"uint(\d*)", t)
    if m:
        n = int(m.group(1) or "256")
        w = _arg_as_word(arg)
        if w is not None and 0 <= w < (1 << n):
            return None
        return f"{t} arg out of range [0, 2^{n}): {arg!r}"
    m = _rex.fullmatch(r"int(\d*)", t)
    if m:
        n = int(m.group(1) or "256")
        v = _arg_as_signed(arg)
        if v is not None and -(1 << (n - 1)) <= v < (1 << (n - 1)):
            return None
        return f"{t} arg out of signed range: {arg!r}"
    if t == "address" or t.startswith("contract ") or t.startswith("interface "):
        w = _arg_as_word(arg)
        if w is not None and 0 <= w < (1 << 160):
            return None
        return f"address/contract arg out of range [0, 2^160): {arg!r}"
    if t == "bytes32":
        # every 32-byte value is a valid bytes32 (no padding constraint), BUT it
        # must be given in the WORD form. The {"bytes":..} form is out (audit
        # finding, CONTEST-BREAKING): measure._encode_arg ALWAYS encodes {bytes}
        # as a DYNAMIC value (offset+length+data), so a static bytes32 parameter
        # decodes the head word as the OFFSET (0x20) on the EVM, while solidity-lean
        # gets a Value.bytes — two different logical calls, a fabricated divergence.
        # A bytes32 value must be passed as {"word": <int>} (static 32-byte head).
        # It must ALSO fit in 32 bytes: measure._encode_arg reduces the word
        # `% (1 << 256)` while render_lean_arg emits the RAW Nat, so a word >= 2^256
        # feeds the two engines DIFFERENT logical calls (EVM sees the truncation,
        # solidity-lean the full magnitude) -> a fabricated divergence. Bound it to
        # the bytes32 domain [0, 2^256), exactly as the uintN branch bounds its word.
        w = _arg_as_word(arg)
        if w is not None and 0 <= w < (1 << 256):
            return None
        return (f"bytes32 arg requires the word form {{\"word\": n}} in [0, 2^256), "
                f"got {arg!r}")
    if t.startswith("enum "):
        canonical = t[len("enum "):].strip()
        count = enum_counts.get(canonical)
        w = _arg_as_word(arg)
        if count is not None and w is not None and 0 <= w < count:
            return None
        if count is None:
            return "__OOS__"   # can't resolve member count -> not validatable
        return f"enum {canonical} arg out of range [0, {count}): {arg!r}"
    # bytesN (N<32), fixed-point, function types, and anything else word-family we
    # cannot faithfully bound from the type string alone -> out of scope.
    return "__OOS__"


_FUEL_CAP = 100_000


def _valid_fuel(value: object) -> Optional[int]:
    """Return a validated fuel (positive int <= cap), or None if malformed
    (review finding 3: an attacker-controlled `fuel` of -1 / 10**12 either fails
    to elaborate or times out, and was mis-scored as a coverage gap)."""
    try:
        fuel = int(value)
    except (TypeError, ValueError):
        return None
    if fuel < 1 or fuel > _FUEL_CAP:
        return None
    return fuel


_UINT256_MAX = (1 << 256) - 1


def _valid_value(value: object) -> Optional[int]:
    """Validate entry.value as an integer msg.value in [0, 2**256). Accepts a
    bool as 0/1 is REJECTED (a JSON bool is not a wei amount). Returns None on a
    non-integer / out-of-range value so the caller can REJECT_MALFORMED instead
    of crashing (audit finding: `int('abc')` raised an uncaught ValueError)."""
    if isinstance(value, bool):
        return None
    if not isinstance(value, int):
        return None
    if value < 0 or value > _UINT256_MAX:
        return None
    return value


_MAX_SLOTS = 64


def _valid_slots(slots: object) -> tuple[Optional[list[int]], Optional[str]]:
    """Validate claim.observed_slots: a list of <=64 non-negative uint256 storage
    slots to compare (§3.4 component 5). Empty/absent means storage is not
    compared. Attacker-controlled -> validated before reaching codegen."""
    if slots is None:
        return [], None
    if not isinstance(slots, list) or len(slots) > _MAX_SLOTS:
        return None, f"observed_slots must be a list of <= {_MAX_SLOTS} slots"
    out: list[int] = []
    for s in slots:
        try:
            v = int(s)
        except (TypeError, ValueError):
            return None, f"observed_slots entry not an integer: {s!r}"
        if v < 0 or v >= (1 << 256):
            return None, f"observed_slots entry out of uint256 range: {s!r}"
        out.append(v)
    return out, None


def _safe_render_args(args: object) -> tuple[Optional[str], Optional[str]]:
    """Render entry args to a Lean list, catching any malformed shape (review
    finding 5: `render_lean_arg` raises on unsupported forms and would crash the
    adjudicator instead of returning REJECT_MALFORMED)."""
    if not isinstance(args, list):
        return None, f"entry.args must be a list, got {type(args).__name__}"
    try:
        return obs.render_lean_args(args), None
    except (ValueError, TypeError, KeyError) as exc:
        return None, f"malformed entry.args: {exc}"


def _test_asts(root: Path, solc: str) -> list[gate.SourceAst]:
    """solc ASTs of the submission's TEST files (review P0 #3 cheatcode scan).

    Test files import ``../src/*``, so they are compiled together with the src
    sources (multi_source_asts) for imports to resolve."""
    test_dir = root / "test"
    if not test_dir.is_dir():
        return []
    test_files = sorted(test_dir.glob("*.sol"))
    src_files = sorted((root / "src").glob("*.sol")) if (root / "src").is_dir() else []
    if not test_files:
        return []
    return gate.multi_source_asts(test_files, test_files + src_files, solc)


def _src_for(sources: list[Path], contract: str, solc: str) -> Optional[Path]:
    return _source_of_contract(sources, contract, solc)


def _source_of_contract(sources: list[Path], contract: str, solc: str) -> Optional[Path]:
    for src in sources:
        try:
            _name, ast = gate._IMPORTER.run_solc_ast(solc, src)
        except Exception:
            # solc-rejected source (the OVER_ACCEPT lane): the contract still
            # exists syntactically — resolve it from the parse-only AST.
            try:
                ast = gate.get_source_asts_parse_only([src], solc=solc)[0].ast
            except Exception:
                continue
        for node in gate.iter_nodes(ast):
            if node.get("nodeType") == "ContractDefinition" and node.get("name") == contract:
                return src
    return None


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Adjudicate a divergence-contest submission")
    p.add_argument("submission", type=Path)
    p.add_argument("--solc", default=hb.DEFAULT_SOLC)
    p.add_argument("--forge", default=hb.DEFAULT_FORGE)
    p.add_argument("--lake", default=hb.DEFAULT_LAKE)
    p.add_argument("--timeout", type=int, default=400)
    p.add_argument("--work-dir", type=Path, default=None)
    p.add_argument("--skip-forge", action="store_true",
                   help="skip the Forge real-behavior check (debug only)")
    p.add_argument("--json", action="store_true", help="emit JSON only")
    args = p.parse_args(argv)

    tools = hb.ToolPaths(solc=args.solc, forge=args.forge, lake=args.lake)
    report = adjudicate(args.submission, tools=tools, work_dir=args.work_dir,
                        timeout=args.timeout, skip_forge=args.skip_forge)
    if args.json:
        print(json.dumps(report.to_dict(), indent=2))
    else:
        print(json.dumps(report.to_dict(), indent=2))
        print(f"\n=== VERDICT: {report.verdict}"
              + (f" (lane {report.lane})" if report.lane else "")
              + f" | qualifies={report.qualifies} ===", file=sys.stderr)
    return 0 if report.qualifies or report.verdict == "NO_DIVERGENCE" else 1


if __name__ == "__main__":
    raise SystemExit(_main())
