// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Malformed-input guard: a bare negative integer arg (-5, NOT the {"int": -5}
// form) is an ill-formed word — measure two's-complements it while the Lean
// renderer emits `Value.word -5` and fails to elaborate. Must be caught as
// REJECT_MALFORMED, never routed to a NEEDS_REVIEW Lean crash.
contract Signer {
    function f(int8 a) external pure returns (int8) {
        return a;
    }
}
