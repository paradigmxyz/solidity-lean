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
    review, not auto-paid.
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

end SolidCore.Solidity.Contest
"""


# The marker the adjudicator greps the #eval output for.
OBSERVABLE_MARKER = "CONTEST_OBS "


def lean_eval_line(namespace: str, contract: str, fuel: int, fname: str,
                   args_lean: str, env: "cenv.EnvOverrides") -> str:
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
    call = f"SolidCore.Solidity.Contest.renderCallResult {do_block}"
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


def evm_observable(ok: bool, ret_hex: str, return_types: list[str]) -> "Observable":
    """Build the EVM observable in normal form from the measured raw result."""
    if ok:
        return parse_observable(evm_return_normal_form(ret_hex, return_types))
    return parse_observable(evm_revert_normal_form(ret_hex))


# ---------------------------------------------------------------------------
# Normal-form observable comparison.
# ---------------------------------------------------------------------------

@dataclass
class Observable:
    """A parsed normal-form observable."""

    raw: str

    @property
    def outcome(self) -> str:
        head = self.raw.split("|", 1)[0]
        if head == "success":
            return "success"
        if head == "solidus-reject":
            return "solidus-reject"
        # revert|panic:.. => panic; revert|error/empty/custom/raw => revert
        if head == "revert":
            body = self.raw.split("|", 1)[1] if "|" in self.raw else ""
            if body.startswith("panic:"):
                return "panic"
            return "revert"
        return head

    @property
    def is_solidus_reject(self) -> bool:
        return self.raw.startswith("solidus-reject|")

    @property
    def reject_message(self) -> str:
        return self.raw.split("|", 1)[1] if self.is_solidus_reject else ""

    def normalized(self) -> str:
        return self.raw.strip()

    def to_dict(self) -> dict:
        return {"outcome": self.outcome, "normal_form": self.raw}


def parse_observable(text: str) -> Observable:
    return Observable(raw=text.strip())


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
    if solidus.normalized() == evm.normalized():
        return ObservableComparison(True, solidus, evm)
    # classify the difference for lane-S sub-kind / dedup fingerprint (§4c/§6.2)
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
