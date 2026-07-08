#!/usr/bin/env python3
"""Observable definition, extraction, and comparison (design §3.4).

The observable of a submission is the tuple the harness compares, in order:

  1. Outcome: success vs revert vs panic.
  2. Return data (on success): the entry call's return values.
  3. Revert/panic data (on failure): selector + payload (Error(string),
     Panic(uint256) code, custom error, or empty).
  4. Events: ordered (topics, data). [v1 single-contract: supported in the
     normal form; the primary comparator checks 1-3, which cover every G1-G22
     value/revert divergence. Event/state comparison is exercised structurally
     and extended for the v2 multi-contract closed-world run.]
  5. State: observed storage reads. [same status as events in v1.]

Equality is EXACT on 1-4. GAS IS NEVER PART OF THE OBSERVABLE (that is the whole
of the SEM-GAS / SEM-CLOSEDGAS exclusion).

NORMAL FORM (a single canonical line, Solidus-internals-independent):

    success|<v1>,<v2>,...        # each vi rendered by ``render_value`` below
    revert|empty
    revert|panic:<code-decimal>
    revert|error:<string>
    revert|custom:<name>:<v1>,<v2>,...
    revert|raw:<hexbytes>
    solidus-reject|<message>     # Solidus fail-closed (import/typecheck/exec)

Value rendering (decimal, so it does not depend on Solidus's Repr):
    w:<nat>      uint / address / bytesN / bool(0|1)
    i:<int>      signed int256 (two's-complement decoded)
    b:<hex>      dynamic bytes
    other Values fall back to r:<reprStr> (documented v1 limit).

The Solidus side is computed by a Lean ``#eval`` (``lean_eval_line``) that runs
the entry call under a Context/BlockEnv carrying the CANONICAL pinned env
(contest/env.py). The solc+EVM side is MEASURED from a Foundry harness that
actually performs the entry call under the SAME pinned env and dumps the raw
outcome + return/revert bytes (``contest/measure.py``); those raw bytes are
decoded here (``evm_observable``) into the SAME normal form. This closes review
defect O-1: the EVM observable is measured from the run, NOT the submitter's
``declared_observable`` string (which is now only a sanity cross-check).

PRECISION LIMITS (documented, v1 restricted launch):
  * Custom-error reverts: the EVM side decodes Error(string)/Panic(uint256)/
    empty precisely; a custom error decodes to ``raw:0x<selector+payload>``
    while Solidus renders ``custom:<name>:...`` -> such a comparison is routed to
    review, not auto-scored.
  * Return decoding covers static words (uint/address/bool/bytesN -> w),
    signed ints (-> i) and a single/leading dynamic bytes/string (-> b).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from . import env as cenv


# ---------------------------------------------------------------------------
# The Lean helper emitted into the generated #eval file. It is NEW tooling
# text (it does not modify SolidCore/**); it only consumes public entry points
# (CheckedInput.ownCall, CallResult, RevertData, Value) already exported by the
# semantics. It renders the §3.4 observable of a single-contract entry call into
# the normal form above.
# ---------------------------------------------------------------------------

LEAN_OBSERVABLE_HELPER = r"""
namespace SolidCore.Solidity.Contest

open SolidCore.Solidity.Source

partial def renderValue (v : SolidCore.Solidity.Source.Value) : String :=
  match v with
  | Value.word w => "w:" ++ toString (SolidCore.Solidity.Shared.norm w)
  | Value.int w =>
      "i:" ++ toString (SolidCore.Solidity.Shared.signedValue w)
  | Value.bytes bs =>
      "b:0x" ++ String.join (bs.map (fun byte =>
        let h := Nat.toDigits 16 (byte % 256)
        let s := String.mk h
        if s.length == 1 then "0" ++ s else s))
  | Value.fixedArray xs => "[" ++ String.intercalate "," (xs.map renderValue) ++ "]"
  | Value.dynamicArray xs => "[" ++ String.intercalate "," (xs.map renderValue) ++ "]"
  | Value.tuple xs => "(" ++ String.intercalate "," (xs.map renderValue) ++ ")"
  | other => "r:" ++ reprStr other

def renderValues (vs : List SolidCore.Solidity.Source.Value) : String :=
  String.intercalate "," (vs.map renderValue)

def renderRevert (rd : SolidCore.Solidity.Source.RevertData) : String :=
  match rd with
  | RevertData.empty => "empty"
  | RevertData.panic w => "panic:" ++ toString (SolidCore.Solidity.Shared.norm w)
  | RevertData.error s => "error:" ++ s
  | RevertData.custom name vs => "custom:" ++ name ++ ":" ++ renderValues vs
  | RevertData.raw bs =>
      "raw:0x" ++ String.join (bs.map (fun byte =>
        let h := Nat.toDigits 16 (byte % 256)
        let s := String.mk h
        if s.length == 1 then "0" ++ s else s))

def renderCallResult
    (r : Except SolidCore.Solidity.TypeCheck.TypeError
                SolidCore.Solidity.Source.CallResult) : String :=
  match r with
  | Except.error e => "solidus-reject|" ++ reprStr e
  | Except.ok (CallResult.returned _ vals) => "success|" ++ renderValues vals
  | Except.ok (CallResult.reverted _ rd) => "revert|" ++ renderRevert rd

-- Components 4 (events) and 5 (observed storage) of the §3.4 observable. Both
-- are extracted from the post-call State and rendered decimal/hex so they match
-- the Foundry-measured EVM side byte-for-byte (contest/measure.py). They are
-- compared ONLY on success: on revert the EVM rolls back logs + storage, so a
-- reverted observable is outcome + revert data only (components 1+3).
def hexOfBytes (bs : List Nat) : String :=
  "0x" ++ String.join (bs.map (fun byte =>
    let h := Nat.toDigits 16 (byte % 256)
    let s := String.mk h
    if s.length == 1 then "0" ++ s else s))

def renderEvents (self : SolidCore.Solidity.Source.Word)
    (state : SolidCore.Solidity.Source.State) : String :=
  let entries := SolidCore.Solidity.Source.State.logEntries state self
  String.intercalate "~" (entries.map (fun e =>
    "t=[" ++ String.intercalate ","
        (e.topics.map (fun w => toString (SolidCore.Solidity.Shared.norm w)))
      ++ "];d=" ++ hexOfBytes e.data))

def renderStorage (slots : List SolidCore.Solidity.Source.Word)
    (state : SolidCore.Solidity.Source.State) : String :=
  String.intercalate ";" (slots.map (fun s =>
    toString (SolidCore.Solidity.Shared.norm s) ++ ":"
      ++ toString (SolidCore.Solidity.Shared.norm
           (SolidCore.Solidity.Source.State.loadSlot state s))))

def renderFull (self : SolidCore.Solidity.Source.Word)
    (slots : List SolidCore.Solidity.Source.Word)
    (r : Except SolidCore.Solidity.TypeCheck.TypeError
                SolidCore.Solidity.Source.CallResult) : String :=
  match r with
  | Except.error e => "solidus-reject|" ++ reprStr e
  | Except.ok res =>
    let outcome := renderCallResult (Except.ok res)
    let evs := match res with
      | CallResult.returned state _ => renderEvents self state
      | CallResult.reverted _ _ => ""
    let sto := match res with
      | CallResult.returned state _ => renderStorage slots state
      | CallResult.reverted _ _ => ""
    outcome ++ "##EVT##" ++ evs ++ "##STO##" ++ sto

end SolidCore.Solidity.Contest
"""


# The marker the adjudicator greps the #eval output for.
OBSERVABLE_MARKER = "CONTEST_OBS "


def lean_eval_line(namespace: str, contract: str, fuel: int, fname: str,
                   args_lean: str, env: "cenv.EnvOverrides",
                   slots: Optional[list[int]] = None) -> str:
    """Build the ``#eval`` that prints the env-pinned observable (review P0 #2).

    The entry call runs through ``CheckedContract.callFunctionWithContext`` under
    a Context derived from the imported contract's own default context with the
    CANONICAL pinned env (block/tx/self/sender) overlaid - the SAME values the
    Foundry measurement harness uses - so env-reading observables agree by
    construction. This uses ONLY public semantics entry points
    (``CheckedInput.program`` / ``CheckedProgram.contract`` /
    ``CheckedContract.callFunctionWithContext``); it does not modify SolidCore.

    ``args_lean`` is a Lean list expression of CoreValue (see render_lean_args).
    """
    TC = "SolidCore.Solidity.TypeCheck"
    src = f"{namespace}.importedSourceUnit"
    self_addr = env.self_addr if env.self_addr is not None else cenv.CANONICAL_SENDER
    slots_lean = "[" + ", ".join(str(int(s)) for s in (slots or [])) + "]"
    do_block = (
        f"(do\n"
        f"    let source := {src}\n"
        f"    let program ← {TC}.CheckedInput.program source\n"
        f"    let contract ← {TC}.CheckedProgram.contract program \"{contract}\"\n"
        f"    let base := contract.core.context\n"
        f"    let ctx := {{ base with\n"
        f"      sender := {env.sender}, self := {self_addr}, value := {env.value},\n"
        f"      accountBalances := base.accountBalances ++ {env.lean_balances()},\n"
        f"      blockEnv := {{ base.blockEnv with {env.lean_block_fields()} }},\n"
        f"      txEnv := {{ base.txEnv with {env.lean_tx_fields()} }} }}\n"
        f"    {TC}.CheckedContract.callFunctionWithContext {fuel}\n"
        f"      contract \"{fname}\" ctx SolidCore.Solidity.Source.State.empty {args_lean})")
    call = (f"SolidCore.Solidity.Contest.renderFull "
            f"{self_addr} {slots_lean} {do_block}")
    return f'#eval "{OBSERVABLE_MARKER.strip()} " ++ ({call})'


# ---------------------------------------------------------------------------
# Python-side rendering of entry args into Lean CoreValue expressions.
# ---------------------------------------------------------------------------

def render_lean_arg(arg: object) -> str:
    """Render a single claim.json entry arg as a Lean CoreValue expression.

    Supported v1 arg forms (documented in README):
      * int (>=0)              -> Value.word n
      * {"word": n}            -> Value.word n
      * {"int": n}             -> Value.int (signedToWord n)   (n may be negative)
      * bool                   -> Value.word 0|1
      * {"bytes": "0x.."}      -> Value.bytes [..]
    """
    V = "SolidCore.Solidity.Source.Value"
    if isinstance(arg, bool):
        return f"({V}.word {1 if arg else 0})"
    if isinstance(arg, int):
        return f"({V}.word {arg})"
    if isinstance(arg, dict):
        if "word" in arg:
            return f"({V}.word {int(arg['word'])})"
        if "int" in arg:
            n = int(arg["int"])
            return f"({V}.int (SolidCore.Solidity.Shared.signedToWord ({n})))"
        if "bytes" in arg:
            hexstr = str(arg["bytes"])
            if hexstr.startswith("0x"):
                hexstr = hexstr[2:]
            byte_list = ", ".join(str(int(hexstr[i:i + 2], 16))
                                  for i in range(0, len(hexstr), 2))
            return f"({V}.bytes [{byte_list}])"
    raise ValueError(f"unsupported entry arg form: {arg!r}")


def render_lean_args(args: list) -> str:
    return "[" + ", ".join(render_lean_arg(a) for a in args) + "]"


# ---------------------------------------------------------------------------
# EVM-side observable, DECODED from the measured Foundry run (review P0 #1).
# The measurement harness (contest/measure.py) dumps the raw entry-call
# (ok, ret-bytes); we decode them into the SAME normal form Solidus renders, so
# the comparator diffs two independently-computed observables.
# ---------------------------------------------------------------------------

_ERROR_SELECTOR = "08c379a0"   # Error(string)
_PANIC_SELECTOR = "4e487b71"   # Panic(uint256)


def _clean_type(t: str) -> str:
    for suffix in (" memory", " storage", " calldata", " payable"):
        t = t.replace(suffix, "")
    return t.strip()


def _is_dynamic(t: str) -> bool:
    t = _clean_type(t)
    return t in ("bytes", "string") or t.endswith("[]")


def render_word_for_type(word: int, t: str) -> str:
    t = _clean_type(t)
    if t.startswith("int") and not t.startswith("uint"):
        # two's-complement decode to a signed int (matches Solidus `i:`).
        if word >= (1 << 255):
            word -= (1 << 256)
        return f"i:{word}"
    return f"w:{word}"


def evm_return_normal_form(ret_hex: str, return_types: list[str]) -> str:
    """Decode ABI-encoded return bytes into `success|<v1>,<v2>,...`."""
    data = bytes.fromhex(ret_hex[2:] if ret_hex.startswith("0x") else ret_hex)
    if not return_types:
        return "success|"
    rendered: list[str] = []
    for i, t in enumerate(return_types):
        head = data[i * 32:(i + 1) * 32]
        word = int.from_bytes(head, "big") if head else 0
        if _is_dynamic(t):
            off = word
            length = int.from_bytes(data[off:off + 32], "big")
            payload = data[off + 32:off + 32 + length]
            rendered.append("b:0x" + payload.hex())
        else:
            rendered.append(render_word_for_type(word, t))
    return "success|" + ",".join(rendered)


def evm_revert_normal_form(ret_hex: str) -> str:
    """Decode revert bytes into `revert|empty|error:..|panic:..|raw:..`."""
    data = bytes.fromhex(ret_hex[2:] if ret_hex.startswith("0x") else ret_hex)
    if len(data) == 0:
        return "revert|empty"
    selector = data[:4].hex()
    if selector == _ERROR_SELECTOR and len(data) >= 4 + 64:
        off = int.from_bytes(data[4:36], "big")
        base = 4 + off
        length = int.from_bytes(data[base:base + 32], "big")
        msg = data[base + 32:base + 32 + length].decode("utf-8", errors="replace")
        return f"revert|error:{msg}"
    if selector == _PANIC_SELECTOR and len(data) >= 4 + 32:
        code = int.from_bytes(data[4:36], "big")
        return f"revert|panic:{code}"
    return "revert|raw:0x" + data.hex()


def evm_observable(ok: bool, ret_hex: str, return_types: list[str],
                   events: Optional[str] = None,
                   storage: Optional[str] = None) -> "Observable":
    """Build the EVM observable in normal form from the measured raw result.

    ``events``/``storage`` are the measured §3.4 components 4/5 (empty string
    when the call reverted); they are appended in the same ``##EVT##``/``##STO##``
    tokenized form the Solidus helper (``renderFull``) emits, so the comparator
    diffs them component-by-component."""
    if ok:
        line = evm_return_normal_form(ret_hex, return_types)
    else:
        line = evm_revert_normal_form(ret_hex)
    if events is not None or storage is not None:
        line = f"{line}{_EVT_SEP}{events or ''}{_STO_SEP}{storage or ''}"
    return parse_observable(line)


# ---------------------------------------------------------------------------
# Normal-form observable comparison.
# ---------------------------------------------------------------------------

_EVT_SEP = "##EVT##"
_STO_SEP = "##STO##"


def _split_sections(raw: str) -> tuple[str, Optional[str], Optional[str]]:
    """Split a raw normal form into (outcome_line, events, storage). The events
    and storage sections are optional (absent on a solidus-reject, or when the
    engine did not emit them)."""
    storage = None
    events = None
    text = raw
    if _STO_SEP in text:
        text, storage = text.split(_STO_SEP, 1)
    if _EVT_SEP in text:
        text, events = text.split(_EVT_SEP, 1)
    return text, events, storage


@dataclass
class Observable:
    """A parsed normal-form observable (outcome line + optional events/storage)."""

    raw: str

    @property
    def outcome_line(self) -> str:
        """The outcome+value/revert section, without events/storage."""
        return _split_sections(self.raw)[0]

    @property
    def events(self) -> Optional[str]:
        return _split_sections(self.raw)[1]

    @property
    def storage(self) -> Optional[str]:
        return _split_sections(self.raw)[2]

    @property
    def outcome(self) -> str:
        head = self.outcome_line.split("|", 1)[0]
        if head == "success":
            return "success"
        if head == "solidus-reject":
            return "solidus-reject"
        # revert|panic:.. => panic; revert|error/empty/custom/raw => revert
        if head == "revert":
            line = self.outcome_line
            body = line.split("|", 1)[1] if "|" in line else ""
            if body.startswith("panic:"):
                return "panic"
            return "revert"
        return head

    @property
    def is_solidus_reject(self) -> bool:
        return self.raw.startswith("solidus-reject|")

    @property
    def reject_message(self) -> str:
        return self.outcome_line.split("|", 1)[1] if self.is_solidus_reject else ""

    def normalized(self) -> str:
        return self.raw.strip()

    def to_dict(self) -> dict:
        return {"outcome": self.outcome, "normal_form": self.raw,
                "outcome_line": self.outcome_line,
                "events": self.events, "storage": self.storage}


def parse_observable(text: str) -> Observable:
    return Observable(raw=text.strip())


def perturb_leading_value(o: "Observable") -> "Observable":
    """Return a copy of ``o`` with its leading ``w:N`` value incremented by one.

    This exists ONLY for the fault-injection SELF-TEST (contest/run_samples.py):
    it lets the full live pipeline exercise a genuine SOUNDNESS_GAP by injecting a
    one-unit delta at the observable boundary, so the divergence-DETECTION path is
    tested end-to-end WITHOUT ever shipping a bug in Solidus. It is never used in
    real adjudication."""
    import re
    m = re.search(r"w:(\d+)", o.outcome_line)
    if not m:
        return Observable(raw=o.raw)
    new_line = o.outcome_line[:m.start()] + f"w:{int(m.group(1)) + 1}" + \
        o.outcome_line[m.end():]
    tail = o.raw[len(o.outcome_line):]
    return Observable(raw=new_line + tail)


@dataclass
class ObservableComparison:
    equal: bool
    solidus: Observable
    evm: Observable
    differing_component: Optional[str] = None  # value/revert/panic/outcome

    def to_dict(self) -> dict:
        d = {
            "equal": self.equal,
            "solidus_observable": self.solidus.to_dict(),
            "evm_observable": self.evm.to_dict(),
        }
        if self.differing_component:
            d["differing_component"] = self.differing_component
        return d


def compare_observables(solidus: Observable, evm: Observable) -> ObservableComparison:
    # Compare COMPONENT BY COMPONENT (§3.4), in order: outcome+return/revert
    # (1-3), then events (4), then observed storage (5). Gas is never compared.
    if solidus.outcome_line.strip() != evm.outcome_line.strip():
        # classify the outcome/value/revert difference for lane-S sub-kind.
        if solidus.outcome != evm.outcome:
            if {solidus.outcome, evm.outcome} & {"success"} and \
               {solidus.outcome, evm.outcome} & {"revert", "panic"}:
                component = "revert-vs-success"
            elif "panic" in (solidus.outcome, evm.outcome):
                component = "wrong-panic"
            else:
                component = "wrong-revert"
        else:
            if solidus.outcome == "success":
                component = "wrong-value"
            elif solidus.outcome == "panic":
                component = "wrong-panic"
            else:
                component = "wrong-revert"
        return ObservableComparison(False, solidus, evm, differing_component=component)

    # Outcome + return/revert agree. On SUCCESS also compare events (4) and
    # observed storage (5); both are rolled back on revert, so not compared then.
    if solidus.outcome == "success":
        s_ev, e_ev = solidus.events, evm.events
        if s_ev is not None and e_ev is not None and s_ev.strip() != e_ev.strip():
            return ObservableComparison(False, solidus, evm,
                                        differing_component="wrong-events")
        s_st, e_st = solidus.storage, evm.storage
        if s_st is not None and e_st is not None and s_st.strip() != e_st.strip():
            return ObservableComparison(False, solidus, evm,
                                        differing_component="wrong-state")
    return ObservableComparison(True, solidus, evm)
