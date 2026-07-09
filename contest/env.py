#!/usr/bin/env python3
"""Canonical environment + cheatcode policy (v1.1 hardening, review P0 #2/#3).

Two contest-breaking defects the adversarial review (commit 368468a) found:

  * E-1 - the block/tx/self environment was NOT pinned across the two engines
    (solidity-lean ran from a zero env, Foundry from its non-zero defaults), so any
    ``block.*`` / ``msg.sender`` / ``tx.origin`` / ``address(this)`` observable
    diverged for a NON-semantic reason.
  * O-3 (env part) - cheatcodes in the submitter's TEST file were unrestricted
    and invisible to the gate, letting the test forge state/oracle values.

This module is the single source of truth for BOTH fixes:

  1. ``CANONICAL_ENV`` / ``CANONICAL_SENDER`` / ``CANONICAL_ORIGIN`` - the ONE
     pinned environment, taken from Foundry's REAL defaults (measured on
     2026-07-08 with forge 1.5.1 + solc 0.8.35, evm_version=cancun; see the
     `docs` changelog note). Both engines run under these identical values.
  2. ``CHEATCODE_ALLOW`` / ``CHEATCODE_DENY`` - the whitelist of env-pinning /
     setup cheatcodes (mirrored into the solidity-lean context) and the default-deny
     of everything state/oracle-forging.
  3. ``EnvOverrides`` - the per-submission env, = ``CANONICAL_ENV`` overlaid with
     the whitelisted cheatcodes' effects, applied IDENTICALLY on both sides.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional


# ---------------------------------------------------------------------------
# The canonical environment == Foundry's real defaults (measured, not guessed).
#   forge 1.5.1-stable, solc 0.8.35, evm_version = cancun.
#   A tiny forge test emitting each field returned exactly these values.
# ---------------------------------------------------------------------------

CANONICAL_ENV: dict[str, int] = {
    "number": 1,                 # block.number
    "timestamp": 1,              # block.timestamp
    "chainid": 31337,            # block.chainid
    "basefee": 0,                # block.basefee
    "coinbase": 0,               # block.coinbase (address 0x0)
    "prevrandao": 0,             # block.prevrandao
    "gaslimit": 1073741824,      # block.gaslimit (0x40000000)
}

# Foundry's default caller / tx.origin (`DEFAULT_SENDER`).
CANONICAL_SENDER = 0x1804c8AB1F12E6bbf3894d4083f33e07309d1f38
CANONICAL_ORIGIN = 0x1804c8AB1F12E6bbf3894d4083f33e07309d1f38
CANONICAL_GASPRICE = 0


# ---------------------------------------------------------------------------
# Cheatcode policy (review P0 #3 + the maintainer's decision).
# ---------------------------------------------------------------------------

# ALLOWED: environment-pinning / setup cheatcodes. Their effect is MIRRORED into
# the solidity-lean context so both sides see the same env. Maps cheatcode -> the env
# field it overrides ("_" = handled specially, not a plain block field).
CHEATCODE_ALLOW: dict[str, str] = {
    "roll": "number",           # vm.roll(uint)      -> block.number
    "warp": "timestamp",        # vm.warp(uint)      -> block.timestamp
    "chainId": "chainid",       # vm.chainId(uint)   -> block.chainid
    "fee": "basefee",           # vm.fee(uint)       -> block.basefee
    "prevrandao": "prevrandao", # vm.prevrandao(b32) -> block.prevrandao
    "prank": "_sender",         # vm.prank(addr)     -> msg.sender (next call)
    "startPrank": "_sender",    # vm.startPrank(addr)-> msg.sender
    "stopPrank": "_noop",       # vm.stopPrank()     -> clears prank (no-op mirror)
    "deal": "_deal",            # vm.deal(addr,amt)  -> balance
}

# Cheatcodes that are harmless observ-ability no-ops (console logging etc.) and
# are simply ignored (neither mirrored nor rejected).
CHEATCODE_IGNORE: set[str] = {"label", "toString", "assume"}

# Explicitly-named BANNED cheatcodes (documentation; the gate is DEFAULT-DENY so
# anything not in ALLOW/IGNORE is rejected regardless of this list).
CHEATCODE_DENY: set[str] = {
    "store", "load",                     # forge arbitrary storage
    "mockCall", "mockCallRevert", "clearMockedCalls",
    "ffi",                               # arbitrary host process
    "etch",                              # forge arbitrary code
    "expectRevert", "expectEmit", "expectCall",
    "record", "accesses",
    "readFile", "writeFile", "removeFile",  # submitter FS (the harness's own
                                            # measurement test may use writeFile,
                                            # but a SUBMISSION test may not)
    "sign", "addr", "deriveKey",
    "setNonce", "resetNonce",
    "coinbase", "txGasPrice",            # not mirrorable in v1 -> deny
}


@dataclass
class EnvOverrides:
    """The canonical env overlaid with a submission's whitelisted cheatcodes.

    Applied IDENTICALLY on both engines: the Foundry measurement harness replays
    these as cheatcodes, and the solidity-lean ``#eval`` threads them into the
    Context/BlockEnv. ``self`` is filled in after the measurement (the deployed
    entry-contract address) so ``address(this)`` agrees by construction."""

    number: int = CANONICAL_ENV["number"]
    timestamp: int = CANONICAL_ENV["timestamp"]
    chainid: int = CANONICAL_ENV["chainid"]
    basefee: int = CANONICAL_ENV["basefee"]
    coinbase: int = CANONICAL_ENV["coinbase"]
    prevrandao: int = CANONICAL_ENV["prevrandao"]
    gaslimit: int = CANONICAL_ENV["gaslimit"]
    sender: int = CANONICAL_SENDER
    origin: int = CANONICAL_ORIGIN
    gasprice: int = CANONICAL_GASPRICE
    value: int = 0
    # self (the entry contract's own address) is measured from the Forge deploy
    # and mirrored so address(this) agrees; None until the measurement runs.
    self_addr: Optional[int] = None
    # vm.deal(addr, amount) balances, mirrored into solidity-lean accountBalances.
    deals: list[tuple[int, int]] = field(default_factory=list)

    def with_self(self, self_addr: int) -> "EnvOverrides":
        self.self_addr = self_addr
        return self

    # -- Lean literals (threaded into the #eval Context/BlockEnv) --------------

    def lean_block_fields(self) -> str:
        return (f"number := {self.number}, timestamp := {self.timestamp}, "
                f"chainid := {self.chainid}, basefee := {self.basefee}, "
                f"coinbase := {self.coinbase}, prevrandao := {self.prevrandao}, "
                f"gaslimit := {self.gaslimit}")

    def lean_tx_fields(self) -> str:
        return f"gasprice := {self.gasprice}, origin := {self.origin}"

    def lean_balances(self) -> str:
        rows = ", ".join(f"({a}, {amt})" for a, amt in self.deals)
        return f"[{rows}]"

    def to_dict(self) -> dict:
        return {
            "number": self.number, "timestamp": self.timestamp,
            "chainid": self.chainid, "basefee": self.basefee,
            "coinbase": self.coinbase, "prevrandao": self.prevrandao,
            "gaslimit": self.gaslimit, "sender": hex(self.sender),
            "origin": hex(self.origin), "value": self.value,
            "self": hex(self.self_addr) if self.self_addr is not None else None,
            "deals": [[hex(a), amt] for a, amt in self.deals],
        }
