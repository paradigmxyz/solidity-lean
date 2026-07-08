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

The Solidus side is computed by a Lean ``#eval`` of the helper this module
emits (``lean_observable_helper``). The solc+EVM side is taken from the
Forge-VALIDATED claim (``declared_observable``), because the Forge test must
PASS on pinned solc+Foundry (design §4 step 1) before Solidus is consulted -
so the declared value is proven real. PRECISION LIMIT: v1 does not re-parse the
full observable tuple out of Foundry traces; it trusts the Forge-passing claim's
normal-form string. Parsing events/state directly from Foundry is a v1.x item.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional


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

/-- Run a single-contract entry call and render its §3.4 observable in the
    contest normal form. A fail-closed Except.error (typecheck / elaboration /
    over-reject) renders as `solidus-reject|...`, which the adjudicator maps to
    a COVERAGE_GAP. -/
def observeCall (fuel : Nat) (decl : SolidCore.Solidity.TypeCheck.SourceContractDecl)
    (fname : String)
    (state : SolidCore.Solidity.TypeCheck.CoreState)
    (args : List SolidCore.Solidity.TypeCheck.CoreValue) : String :=
  match SolidCore.Solidity.TypeCheck.CheckedInput.ownCall fuel decl
      (SolidCore.Solidity.Source.CallTarget.name fname) state args with
  | Except.error e => "solidus-reject|" ++ reprStr e
  | Except.ok (CallResult.returned _ vals) => "success|" ++ renderValues vals
  | Except.ok (CallResult.reverted _ rd) => "revert|" ++ renderRevert rd

end SolidCore.Solidity.Contest
"""


# The marker the adjudicator greps the #eval output for.
OBSERVABLE_MARKER = "CONTEST_OBS "


def lean_eval_line(namespace: str, fuel: int, fname: str, args_lean: str) -> str:
    """Build the ``#eval`` that prints the observable prefixed with the marker.

    ``args_lean`` is a Lean list expression of CoreValue (see render_lean_args).
    """
    decl = f"{namespace}.importedContract"
    state = "SolidCore.Solidity.Source.State.empty"
    call = (f"SolidCore.Solidity.Contest.observeCall {fuel} {decl} "
            f"\"{fname}\" {state} {args_lean}")
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
