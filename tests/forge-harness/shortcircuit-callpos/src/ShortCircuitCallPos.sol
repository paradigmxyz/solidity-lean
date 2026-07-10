// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// SHORTCIRCUIT-CALL-POS (#131) — the residual of the EXT-CALL-POS family
// (#70/#73/extcall-binary): three call-in-short-circuit / call-in-ternary shapes
// that solc 0.8.35 accepts but solidity-lean previously failed to LOWER:
//
//   1. BOTH operands external calls in `&&`/`||`  (`this.f() && this.g()`).
//   2. EXTERNAL-call ternary CONDITION            (`this.f() ? a : b`).
//   3. A call nested in an OTHERWISE-PURE operand (`h() && (j()+1 > 0)`).
//
// The runtime short-circuit semantics were already correct — this was purely a
// lowering coverage gap. The fix mirrors the both-internal `&&`/`||` hoister for
// both-external, hoists an external-call ternary condition like the internal one,
// and (for call-in-pure-operand) hoists the operand's inner call INSIDE the
// guarded branch so it runs exactly when the lhs selects it.
//
// A `_counter` state var is a SIDE-EFFECT WITNESS: the `*Short` functions arrange
// for the skipped operand to be the one that would bump the counter, so a counter
// that stays 0 PROVES the effectful skipped operand did not execute (short-circuit
// preserved); the `*Run` twins select that operand and leave the counter at 1.
//
// Uses external `this.`-self-calls (STATICCALL for view helpers, CALL for the
// counter-bumping helper) and internal calls, so the contract is self-contained:
// no user-typed state var blocks the solc-AST import, importedContractAccepted
// pins acceptance (lowering), and the Forge test exercises real solc/EVM
// execution + short-circuit against the deployed contract.
contract ShortCircuitCallPosTarget {
    uint256 private _counter;

    function counter() external view returns (uint256) {
        return _counter;
    }

    // External self-call helpers.
    function retTrue() public pure returns (bool) {
        return true;
    }

    function retFalse() public pure returns (bool) {
        return false;
    }

    // Side-effecting external self-call (CALL): bumps the witness, returns true.
    function bumpTrue() public returns (bool) {
        _counter += 1;
        return true;
    }

    // Internal helpers for the call-in-pure-operand case.
    function h() internal pure returns (bool) {
        return true;
    }

    function hF() internal pure returns (bool) {
        return false;
    }

    // Side-effecting internal helper (bumps the witness).
    function jBump() internal returns (uint256) {
        _counter += 1;
        return 5;
    }

    function jPure() internal pure returns (uint256) {
        return 5;
    }

    // --- Case 1: BOTH-EXTERNAL `&&` / `||` (with short-circuit witness) ---

    // lhs false => rhs `this.bumpTrue()` must be SKIPPED (counter stays 0).
    function bothAndShort() external returns (bool) {
        return this.retFalse() && this.bumpTrue();
    }

    // lhs true => rhs `this.bumpTrue()` runs (counter 1).
    function bothAndRun() external returns (bool) {
        return this.retTrue() && this.bumpTrue();
    }

    // lhs true => rhs `this.bumpTrue()` must be SKIPPED (counter stays 0).
    function bothOrShort() external returns (bool) {
        return this.retTrue() || this.bumpTrue();
    }

    // lhs false => rhs `this.bumpTrue()` runs (counter 1).
    function bothOrRun() external returns (bool) {
        return this.retFalse() || this.bumpTrue();
    }

    // Chained both-external `&&` — `(a && b) && c`, all true.
    function chainAnd() external view returns (bool) {
        return this.retTrue() && this.retTrue() && this.retTrue();
    }

    // --- Case 2: EXTERNAL ternary CONDITION (pure branches) ---

    function extTernaryTrue() external view returns (uint256) {
        return this.retTrue() ? 1 : 2; // 1
    }

    function extTernaryFalse() external view returns (uint256) {
        return this.retFalse() ? 1 : 2; // 2
    }

    // --- Case 3: CALL nested in an OTHERWISE-PURE operand ---

    // true && (5+1 > 0) = true.
    function callInPure() external pure returns (bool) {
        return h() && (jPure() + 1 > 0);
    }

    // lhs false => `(jBump()+1 > 0)` must be SKIPPED — jBump() not called
    // (counter stays 0), returns false.
    function callInPureShort() external returns (bool) {
        return hF() && (jBump() + 1 > 0);
    }

    // lhs true => `(jBump()+1 > 0)` runs — jBump() bumps counter (1), returns true.
    function callInPureRun() external returns (bool) {
        return h() && (jBump() + 1 > 0);
    }
}
