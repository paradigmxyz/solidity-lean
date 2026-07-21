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

NORMAL FORM (a single canonical line, solidity-lean-internals-independent):

    success|<v1>,<v2>,...        # each vi rendered by ``render_value`` below
    revert|empty
    revert|panic:<code-decimal>
    revert|error:<string>
    revert|custom:<name>:<v1>,<v2>,...
    revert|raw:<hexbytes>
    deployrevert|<same bodies>   # the CONSTRUCTOR reverted (deploy failed, the
                                 # entry call never ran) — phase-distinct from an
                                 # entry-call revert with identical revert data
    solidity-lean-reject|<message>     # solidity-lean fail-closed (import/typecheck/exec)

Value rendering (decimal, so it does not depend on solidity-lean's Repr):
    w:<nat>      uint / address / bytesN / bool(0|1)
    i:<int>      signed int256 (two's-complement decoded)
    b:<hex>      dynamic bytes
    other Values fall back to r:<reprStr> (documented v1 limit).

The solidity-lean side is computed by a Lean ``#eval`` (``lean_eval_line``) that runs
the entry call under a Context/BlockEnv carrying the CANONICAL pinned env
(contest/env.py). The solc+EVM side is MEASURED from a Foundry harness that
actually performs the entry call under the SAME pinned env and dumps the raw
outcome + return/revert bytes (``contest/measure.py``); those raw bytes are
decoded here (``evm_observable``) into the SAME normal form. This closes review
defect O-1: the EVM observable is measured from the run, NOT the submitter's
``declared_observable`` string (which is now only a sanity cross-check).

PRECISION LIMITS (documented, v1 restricted launch):
  * Custom-error reverts ARE now decoded: given the submission's error
    definitions (name + params + the AST ``errorSelector``), the EVM side renders
    ``revert|custom:<Name>:<v1>,...`` in the same normal form solidity-lean produces, so
    they are compared automatically. A custom error whose selector is not among
    the submission's definitions still falls back to ``raw:0x...``.
  * Return / custom-error arg decoding covers static words (uint/address/bool/
    bytesN/enum/contract -> w), signed ints (-> i) and a single/leading dynamic
    bytes/string (-> b).
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
  | Except.error e => "solidity-lean-reject|" ++ reprStr e
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

-- Broad storage divergence (contest #8): instead of trusting a submitter-declared
-- slot list, dump the ENTIRE post-call storage map. Every slot the contract ever
-- wrote (via constructor, initializer, or the entry call) lives in state.storage
-- (StorageMap = Std.HashMap Word Word, the live self account's slots). We emit all
-- non-zero slots; a slot holding 0 is indistinguishable from never-written, so it
-- is dropped on BOTH sides to keep the comparison symmetric. Order is irrelevant:
-- the comparator parses this into a slot->value map. Mappings/dynamic arrays land
-- at their keccak-derived slots, which both engines compute identically, so they
-- are covered too — no declared slots required.
def renderStorageAll
    (state : SolidCore.Solidity.Source.State) : String :=
  let entries := Std.HashMap.toList state.storage
  String.intercalate ";" (entries.filterMap (fun kv =>
    let v := SolidCore.Solidity.Shared.norm kv.2
    if v == 0 then none
    else some (toString (SolidCore.Solidity.Shared.norm kv.1) ++ ":"
                 ++ toString v)))

def renderFull (self : SolidCore.Solidity.Source.Word)
    (_slots : List SolidCore.Solidity.Source.Word)
    (r : Except SolidCore.Solidity.TypeCheck.TypeError
                SolidCore.Solidity.Source.CallResult) : String :=
  match r with
  | Except.error e => "solidity-lean-reject|" ++ reprStr e
  | Except.ok res =>
    let outcome := renderCallResult (Except.ok res)
    let evs := match res with
      | CallResult.returned state _ => renderEvents self state
      | CallResult.reverted _ _ => ""
    -- Broad storage check (contest #8): dump the WHOLE post-call storage map, not
    -- just declared `slots`. `slots` is retained for signature compatibility and
    -- as an (unused) targeted-subset hook; the full-map dump subsumes it.
    let sto := match res with
      | CallResult.returned state _ => renderStorageAll state
      | CallResult.reverted _ _ => ""
    outcome ++ "##EVT##" ++ evs ++ "##STO##" ++ sto

-- Like renderEvents, but drops the first `skip` log entries — the events emitted
-- during CONSTRUCTION. The EVM measurement arms vm.recordLogs() AFTER the deploy,
-- so its event observable excludes constructor logs; the solidity-lean State
-- accumulates ctor + entry-call logs in one stream, so we skip the post-
-- construction prefix to compare only the ENTRY CALL's events (component 4).
-- (Storage, by contrast, is compared INCLUDING ctor writes on both sides: the EVM
-- arms vm.record() BEFORE the deploy, and renderStorageAll dumps the full map.)
def renderEventsFrom (self : SolidCore.Solidity.Source.Word)
    (state : SolidCore.Solidity.Source.State) (skip : Nat) : String :=
  let entries := (SolidCore.Solidity.Source.State.logEntries state self).drop skip
  String.intercalate "~" (entries.map (fun e =>
    "t=[" ++ String.intercalate ","
        (e.topics.map (fun w => toString (SolidCore.Solidity.Shared.norm w)))
      ++ "];d=" ++ hexOfBytes e.data))

-- renderFull variant that receives the post-construction log count so the event
-- section shows ONLY the entry call's logs (see renderEventsFrom). Storage still
-- dumps the whole map (ctor writes included, symmetric with the EVM side).
-- The Bool flags a CONSTRUCTOR (deploy-phase) revert: the deployment itself
-- failed and the entry call never ran. It renders with the distinct
-- `deployrevert|` head so a deploy-phase revert can NEVER compare equal to an
-- entry-call revert carrying the same revert data (they are different
-- observable outcomes: on the EVM one leaves no contract, the other does).
def renderFullDelta (self : SolidCore.Solidity.Source.Word)
    (_slots : List SolidCore.Solidity.Source.Word)
    (r : Except SolidCore.Solidity.TypeCheck.TypeError
                (Nat × Bool × SolidCore.Solidity.Source.CallResult)) : String :=
  match r with
  | Except.error e => "solidity-lean-reject|" ++ reprStr e
  | Except.ok (ctorLogs, deployReverted, res) =>
    let outcome := match res, deployReverted with
      | CallResult.reverted _ rd, true => "deployrevert|" ++ renderRevert rd
      | _, _ => renderCallResult (Except.ok res)
    let evs := match res with
      | CallResult.returned state _ => renderEventsFrom self state ctorLogs
      | CallResult.reverted _ _ => ""
    let sto := match res with
      | CallResult.returned state _ => renderStorageAll state
      | CallResult.reverted _ _ => ""
    outcome ++ "##EVT##" ++ evs ++ "##STO##" ++ sto

end SolidCore.Solidity.Contest
"""


# The marker the adjudicator greps the #eval output for.
OBSERVABLE_MARKER = "CONTEST_OBS "


def lean_eval_line(namespace: str, contract: str, fuel: int, fname: str,
                   args_lean: str, env: "cenv.EnvOverrides",
                   slots: Optional[list[int]] = None,
                   ctor_args_lean: str = "[]",
                   inject_storage: Optional[list[tuple[int, int]]] = None,
                   calldata_hex: Optional[str] = None) -> str:
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
    WORD = "SolidCore.Solidity.Source.Word"
    STORAGEMAP = "SolidCore.Solidity.Source.StorageMap"
    src = f"{namespace}.importedSourceUnit"
    self_addr = env.self_addr if env.self_addr is not None else cenv.CANONICAL_SENDER
    slots_lean = "[" + ", ".join(str(int(s)) for s in (slots or [])) + "]"
    # Raw storage injection (manifest `storage`): fold the declared (slot, word)
    # pairs into deployState.storage AFTER construction, so the entry call runs from
    # the seeded state. This is the exact mirror of the EVM side's `vm.store` (also
    # applied post-constructor) — State is a total function over storage, so a seeded
    # state need not be reachable by prior execution. Word literals are annotated so
    # the pair list elaborates at `Word × Word` (via OfNat), not `Nat × Nat`.
    inject = inject_storage or []
    seed_pairs = "[" + ", ".join(f"({s}, {w})" for s, w in inject) + "]"
    seed_line = ("" if not inject else
                 f"    let deployState := {{ deployState with storage :=\n"
                 f"      (({seed_pairs} : List ({WORD} × {WORD})).foldl\n"
                 f"        (fun acc kv => {STORAGEMAP}.insertLoop acc kv.1 kv.2)\n"
                 f"        deployState.storage) }}\n")
    # Entry-context calldata: the ENTRY call's real ABI bytes (selector ++
    # encoded args) — the very bytes the Foundry measurement sends — overlaid
    # on the entry context ONLY, so msg.data/msg.sig observables are faithful
    # at the top-level call (d206: the by-name entry used to run with
    # ``calldata := []``). The CONSTRUCTOR context keeps its default empty
    # calldata: on the EVM, creation-time msg.data is empty. Byte = Nat.
    entry_overrides = []
    if calldata_hex:
        cd_bytes = bytes.fromhex(calldata_hex)
        cd_list = "[" + ", ".join(str(b) for b in cd_bytes) + "]"
        entry_overrides.append(f"calldata :=\n      ({cd_list} : List Nat)")
    # Value-carrying entry: revm debits the (pranked) caller AT CALL TIME, so
    # inside the entry call the EVM reads the caller's balance already minus
    # msg.value. Mirror that on the ENTRY context only (the constructor context
    # keeps the undebited seed — the pranked deploy carries no value); see
    # env.EnvOverrides.lean_balances(debit_entry_value=True).
    if env.value:
        entry_overrides.append(
            "accountBalances := base.accountBalances ++ "
            f"{env.lean_balances(debit_entry_value=True)}")
    if entry_overrides:
        # One `let` per override (shadowing re-binds ctxCall): comma-separated
        # multi-field record updates tripped this Lean version's parser when a
        # field value ends in a parenthesized type ascription.
        lines = []
        src_ctx = "ctx"
        for ov_field in entry_overrides:
            lines.append(f"    let ctxCall := {{ {src_ctx} with {ov_field} }}\n")
            src_ctx = "ctxCall"
        cd_line = "".join(lines)
        entry_ctx = "ctxCall"
    else:
        cd_line = ""
        entry_ctx = "ctx"
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
        # Deploy the contract first: run the (possibly synthesized) constructor,
        # which applies state-variable initializers AND explicit constructor
        # bodies, producing the post-construction State. The EVM measurement side
        # deploys with `new C()` (no args, zero value), so we mirror that exactly
        # (empty ctor args, value 0). The entry function is then called against
        # this post-construction State rather than State.empty, so contracts with
        # initialized storage/immutables do NOT produce a spurious divergence.
        f"    let deployState ← match ← {TC}.CheckedContract.constructWithContext {fuel}\n"
        f"        contract ctx SolidCore.Solidity.Source.State.empty {env.sender} 0 {ctor_args_lean} with\n"
        f"      | SolidCore.Solidity.Source.CallResult.returned st _ => pure st\n"
        # A constructor that reverts means the deployment failed: on the EVM the
        # contract never comes into existence. Surface the ctor revert as the
        # observable outcome (short-circuit the entry call), FLAGGED as a
        # deploy-phase revert (the Bool) so it renders `deployrevert|...` —
        # phase-distinct from an entry-call revert with identical revert data.
        f"      | rr@(SolidCore.Solidity.Source.CallResult.reverted _ _) =>\n"
        f"          return (0, true, rr)\n"
        # Seed the manifest `storage` slots into deployState AFTER construction and
        # BEFORE the entry call (mirrors the EVM side's post-constructor vm.store).
        f"{seed_line}"
        # Count the logs emitted during CONSTRUCTION so the observable can show only
        # the ENTRY CALL's events (the EVM side arms recordLogs after the deploy).
        f"    let ctorLogs := (SolidCore.Solidity.Source.State.logEntries deployState {self_addr}).length\n"
        f"{cd_line}"
        f"    let callRes ← {TC}.CheckedContract.callFunctionWithContext {fuel}\n"
        f"      contract \"{fname}\" {entry_ctx} deployState {args_lean}\n"
        f"    pure (ctorLogs, false, callRes))")
    call = (f"SolidCore.Solidity.Contest.renderFullDelta "
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
# (ok, ret-bytes); we decode them into the SAME normal form solidity-lean renders, so
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


def _fixed_bytes_n(t: str) -> Optional[int]:
    """Return N for a `bytesN` (1..32) type, else None. `bytes` (dynamic) -> None."""
    if t.startswith("bytes") and t[5:].isdigit():
        n = int(t[5:])
        if 1 <= n <= 32:
            return n
    return None


def render_word_for_type(word: int, t: str) -> str:
    t = _clean_type(t)
    n = _fixed_bytes_n(t)
    if n is not None:
        # bytesN parity (audit round 2, CONTEST-BREAKING): EVM ABI LEFT-aligns
        # bytesN in the 32-byte head word, but solidity-lean's internal convention
        # is RIGHT-aligned (meaningful bytes low; Interpreter.lean:468-475 stores
        # `norm value % 2^(8N)`). Its observable renders that right-aligned word as
        # `w:`, so we shift the EVM head word right by (256-8N) to match — else a
        # `bytes4` return / custom-error arg like 0x01020304 rendered as
        # w:16909060 (Lean) vs w:(0x01020304<<224) (EVM), a fake SOUNDNESS_GAP.
        # N=32 -> shift 0 (full word, left==right).
        return f"w:{word >> (256 - 8 * n)}"
    if t.startswith("int") and not t.startswith("uint"):
        # two's-complement decode to a signed int (matches solidity-lean `i:`).
        if word >= (1 << 255):
            word -= (1 << 256)
        return f"i:{word}"
    return f"w:{word}"


def _decode_abi_values(data: bytes, types: list[str]) -> list[str]:
    """Decode ABI head/tail-encoded ``data`` for ``types`` into normal-form value
    strings (w:/i:/b:), matching the solidity-lean ``renderValues`` renderer. Static
    words go in the head; a dynamic bytes/string is read via its head offset.
    Addresses/enums/contracts are static words -> ``w:`` (as solidity-lean renders)."""
    rendered: list[str] = []
    for i, t in enumerate(types):
        head = data[i * 32:(i + 1) * 32]
        word = int.from_bytes(head, "big") if head else 0
        if _is_dynamic(t):
            off = word
            length = int.from_bytes(data[off:off + 32], "big")
            payload = data[off + 32:off + 32 + length]
            rendered.append("b:0x" + payload.hex())
        else:
            rendered.append(render_word_for_type(word, t))
    return rendered


def evm_return_normal_form(ret_hex: str, return_types: list[str]) -> str:
    """Decode ABI-encoded return bytes into `success|<v1>,<v2>,...`."""
    data = bytes.fromhex(ret_hex[2:] if ret_hex.startswith("0x") else ret_hex)
    if not return_types:
        return "success|"
    return "success|" + ",".join(_decode_abi_values(data, return_types))


def evm_revert_normal_form(
        ret_hex: str,
        errors: Optional[dict[str, tuple[str, list[str]]]] = None) -> str:
    """Decode revert bytes into `revert|empty|error:..|panic:..|custom:..|raw:..`.

    ``errors`` maps a 4-byte selector (8 lowercase hex, no 0x) to
    ``(error_name, [param_type, ...])`` for the submission's user-defined errors;
    a matching selector is decoded into ``revert|custom:<Name>:<v1>,...`` in the
    SAME normal form solidity-lean's ``renderRevert`` produces, so custom-error reverts
    are compared automatically instead of routed to review."""
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
    if errors and selector in errors:
        name, types = errors[selector]
        try:
            vals = _decode_abi_values(data[4:], types)
            return f"revert|custom:{name}:" + ",".join(vals)
        except Exception:
            pass  # fall through to raw on any decode issue
    return "revert|raw:0x" + data.hex()


def evm_observable(ok: bool, ret_hex: str, return_types: list[str],
                   events: Optional[str] = None,
                   storage: Optional[str] = None,
                   errors: Optional[dict[str, tuple[str, list[str]]]] = None,
                   deploy_reverted: bool = False) -> "Observable":
    """Build the EVM observable in normal form from the measured raw result.

    ``events``/``storage`` are the measured §3.4 components 4/5 (empty string
    when the call reverted); they are appended in the same ``##EVT##``/``##STO##``
    tokenized form the solidity-lean helper (``renderFull``) emits, so the comparator
    diffs them component-by-component.

    ``deploy_reverted`` marks a CONSTRUCTOR (deploy-phase) revert: ``ret_hex``
    is then the constructor's revert data and the normal form gets the distinct
    ``deployrevert|`` head — the same head the solidity-lean helper emits for a
    model-side constructor revert — so deploy-phase and entry-call reverts are
    phase-distinct comparable outcomes."""
    if ok:
        line = evm_return_normal_form(ret_hex, return_types)
    else:
        line = evm_revert_normal_form(ret_hex, errors=errors)
        if deploy_reverted:
            line = "deployrevert|" + line.split("|", 1)[1]
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
    and storage sections are optional (absent on a solidity-lean-reject, or when the
    engine did not emit them).

    Split from the RIGHT (rsplit): the ``##EVT##``/``##STO##`` markers are appended
    STRUCTURALLY after the outcome (``outcome ##EVT## events ##STO## storage``), and
    the events/storage sections are always marker-free (renderEvents emits numeric
    topics + ``hexOfBytes`` data; renderStorage emits ``slot:value`` numeric words).
    The OUTCOME, by contrast, can carry a submitter-controlled raw string — an
    ``Error(string)`` revert reason (``error:`` ++ s) or a custom-error string arg —
    that may itself contain the literal marker text. Splitting on the FIRST marker
    then truncated the outcome at the injected marker, so two DIFFERENT revert
    reasons sharing a pre-marker prefix compared EQUAL — a real wrong-revert
    divergence could be MASKED (comparator over-accept). rsplit keys on the true
    trailing structural markers, leaving an injected outcome intact."""
    storage = None
    events = None
    text = raw
    if _STO_SEP in text:
        text, storage = text.rsplit(_STO_SEP, 1)
    if _EVT_SEP in text:
        text, events = text.rsplit(_EVT_SEP, 1)
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
        if head == "solidity-lean-reject":
            return "solidity-lean-reject"
        # deployrevert|.. => the CONSTRUCTOR reverted (deploy-phase outcome,
        # distinct from an entry-call revert regardless of the revert data).
        if head == "deployrevert":
            return "deployrevert"
        # revert|panic:.. => panic; revert|error/empty/custom/raw => revert
        if head == "revert":
            line = self.outcome_line
            body = line.split("|", 1)[1] if "|" in line else ""
            if body.startswith("panic:"):
                return "panic"
            return "revert"
        return head

    @property
    def is_solidity_lean_reject(self) -> bool:
        return self.raw.startswith("solidity-lean-reject|")

    @property
    def reject_message(self) -> str:
        return self.outcome_line.split("|", 1)[1] if self.is_solidity_lean_reject else ""

    def normalized(self) -> str:
        return self.raw.strip()

    def to_dict(self) -> dict:
        return {"outcome": self.outcome, "normal_form": self.raw,
                "outcome_line": self.outcome_line,
                "events": self.events, "storage": self.storage}


def parse_observable(text: str) -> Observable:
    return Observable(raw=text.strip())


def canonicalize_raw_revert(
        o: "Observable",
        errors: Optional[dict[str, tuple[str, list[str]]]] = None) -> "Observable":
    """Re-decode a ``revert|raw:0x<hex>`` outcome through the SAME revert decoder
    the EVM side uses, so identical revert BYTES canonicalize to identical normal
    forms regardless of which engine happened to emit a structured vs raw revert.

    solidity-lean models a *literal-string* ``require``/``revert`` as a structured
    ``RevertData.error`` (renders ``error:s``), but a *dynamically-built* string
    revert (``revert(string(abi.encodePacked(..)))``) as ``RevertData.raw`` bytes
    (renders ``raw:0x08c379a0..``). The EVM side ALWAYS decodes by selector. Those
    are the SAME revert data, so comparing ``raw:0x08c379a0..`` against ``error:..``
    fabricated a wrong-revert SOUNDNESS_GAP. Decoding the raw bytes here removes the
    representation asymmetry; a genuinely different byte string still decodes to a
    different form, so real divergences are preserved (never masked)."""
    outcome, events, storage = _split_sections(o.raw)
    # Both the entry-call and the deploy-phase (constructor) revert channels can
    # carry a raw form; canonicalize each under its own phase head so the phase
    # distinction is preserved.
    head = None
    for prefix in ("revert|raw:0x", "deployrevert|raw:0x"):
        if outcome.startswith(prefix):
            head = prefix.split("|", 1)[0]
            hexbody = outcome[len(prefix):]
            break
    if head is None:
        return o
    try:
        decoded = evm_revert_normal_form("0x" + hexbody, errors=errors)
    except Exception:
        return o  # undecodable -> leave the raw form untouched
    if decoded.startswith("revert|raw:"):
        return o  # selector unrecognized; no canonical gain, keep original
    if head == "deployrevert":
        decoded = "deployrevert|" + decoded.split("|", 1)[1]
    if events is None and storage is None:
        return Observable(raw=decoded)
    return Observable(raw=f"{decoded}{_EVT_SEP}{events or ''}{_STO_SEP}{storage or ''}")


def perturb_leading_value(o: "Observable") -> "Observable":
    """Return a copy of ``o`` with its leading ``w:N`` value incremented by one.

    This exists ONLY for the fault-injection SELF-TEST (contest/run_samples.py):
    it lets the full live pipeline exercise a genuine SOUNDNESS_GAP by injecting a
    one-unit delta at the observable boundary, so the divergence-DETECTION path is
    tested end-to-end WITHOUT ever shipping a bug in solidity-lean. It is never used in
    real adjudication."""
    import re
    m = re.search(r"w:(\d+)", o.outcome_line)
    if not m:
        return Observable(raw=o.raw)
    new_line = o.outcome_line[:m.start()] + f"w:{int(m.group(1)) + 1}" + \
        o.outcome_line[m.end():]
    tail = o.raw[len(o.outcome_line):]
    return Observable(raw=new_line + tail)


def perturb_storage_slot(o: "Observable") -> "Observable":
    """Return a copy of ``o`` with the value of its first storage slot bumped by 1.

    Fault-injection SELF-TEST twin of :func:`perturb_leading_value`, but for the
    broad storage component (contest #8): it injects a one-unit delta into the
    storage map at the observable boundary so the full pipeline exercises a real
    SOUNDNESS_GAP(wrong-state) WITHOUT shipping any bug in solidity-lean. Never used in
    real adjudication. If there is no storage section, ``o`` is returned as-is."""
    import re
    line, events, storage = _split_sections(o.raw)
    if not storage:
        return Observable(raw=o.raw)
    m = re.match(r"(\d+):(\d+)(.*)$", storage.strip(), re.S)
    if not m:
        return Observable(raw=o.raw)
    slot, val, rest = m.group(1), int(m.group(2)), m.group(3)
    new_storage = f"{slot}:{val + 1}{rest}"
    rebuilt = line
    if events is not None:
        rebuilt += _EVT_SEP + events
    rebuilt += _STO_SEP + new_storage
    return Observable(raw=rebuilt)


@dataclass
class ObservableComparison:
    equal: bool
    solidity_lean: Observable
    evm: Observable
    differing_component: Optional[str] = None  # value/revert/panic/outcome

    def to_dict(self) -> dict:
        d = {
            "equal": self.equal,
            "solidity_lean_observable": self.solidity_lean.to_dict(),
            "evm_observable": self.evm.to_dict(),
        }
        if self.differing_component:
            d["differing_component"] = self.differing_component
        return d


def _parse_storage_map(section: str) -> dict[int, int]:
    """Parse a ``slot:value;slot:value`` storage section into a {slot: value} map.

    Zero-valued slots are dropped so a slot holding 0 compares equal to a slot
    that was never written (the two are indistinguishable on-chain). This makes
    the broad full-map comparison symmetric and order-independent: the solidity-lean
    side dumps its HashMap in arbitrary order, the EVM side dumps vm.accesses
    order, and both normalize to the same canonical map."""
    out: dict[int, int] = {}
    for pair in section.strip().split(";"):
        pair = pair.strip()
        if not pair:
            continue
        k, _, v = pair.partition(":")
        try:
            slot, val = int(k), int(v)
        except ValueError:
            continue
        if val != 0:
            out[slot] = val
    return out


def compare_observables(solidity_lean: Observable, evm: Observable) -> ObservableComparison:
    # Compare COMPONENT BY COMPONENT (§3.4), in order: outcome+return/revert
    # (1-3), then events (4), then observed storage (5). Gas is never compared.
    if solidity_lean.outcome_line.strip() != evm.outcome_line.strip():
        # classify the outcome/value/revert difference for lane-S sub-kind.
        if solidity_lean.outcome != evm.outcome:
            outs = {solidity_lean.outcome, evm.outcome}
            if "deployrevert" in outs:
                # the engines DISAGREE on the deploy outcome: one constructor
                # reverts where the other deploys fine (the entry then runs to
                # success or its own revert) — a deploy-phase divergence.
                component = ("deploy-revert-vs-success" if "success" in outs
                             else "deploy-vs-call-revert")
            elif outs & {"success"} and outs & {"revert", "panic"}:
                component = "revert-vs-success"
            elif "panic" in (solidity_lean.outcome, evm.outcome):
                component = "wrong-panic"
            else:
                component = "wrong-revert"
        else:
            if solidity_lean.outcome == "success":
                component = "wrong-value"
            elif solidity_lean.outcome == "panic":
                component = "wrong-panic"
            elif solidity_lean.outcome == "deployrevert":
                # both constructors revert, but with DIFFERENT revert data.
                component = "wrong-deploy-revert"
            else:
                component = "wrong-revert"
        return ObservableComparison(False, solidity_lean, evm, differing_component=component)

    # Outcome + return/revert agree. On SUCCESS also compare events (4) and
    # observed storage (5); both are rolled back on revert, so not compared then.
    if solidity_lean.outcome == "success":
        s_ev, e_ev = solidity_lean.events, evm.events
        if s_ev is not None and e_ev is not None and s_ev.strip() != e_ev.strip():
            return ObservableComparison(False, solidity_lean, evm,
                                        differing_component="wrong-events")
        s_st, e_st = solidity_lean.storage, evm.storage
        if s_st is not None and e_st is not None and \
                _parse_storage_map(s_st) != _parse_storage_map(e_st):
            return ObservableComparison(False, solidity_lean, evm,
                                        differing_component="wrong-state")
    return ObservableComparison(True, solidity_lean, evm)
