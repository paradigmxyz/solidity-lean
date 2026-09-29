import SolidCore.Solidity.Checked

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
  -- EXTERNAL function value: the model carries (address, selector) — exactly
  -- the two components the EVM ABI packs into its 24-byte left-aligned word.
  -- Render the canonical `f:<addr-decimal>:<selector-decimal>` form; the EVM
  -- decoder (render_word_for_type) unpacks its measured word into the SAME
  -- form, so external function values in the return/revert channel COMPARE
  -- (register 1.4: X-FNVAL narrowed to internal function values, which carry
  -- only a per-contract dispatch ID and are never ABI-encodable).
  | Value.externalFunction addr selector =>
      "f:" ++ toString (SolidCore.Solidity.Shared.norm addr) ++ ":"
        ++ toString (SolidCore.Solidity.Shared.norm selector)
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
