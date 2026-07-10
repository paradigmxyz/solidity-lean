// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// SHORTCIRCUIT-CALL-POS (#131), case 3 — a CALL nested in an OTHERWISE-PURE
// operand of `&&`/`||` (`h() && (j()+1 > 0)`). Purely INTERNAL calls, so the
// contract is EXECUTABLE in the solidity-lean model (no external world needed):
// the companion Lean semantics eval RUNS these in-model and proves short-circuit
// (`skipPanic` returns normally because the div-by-zero in the skipped operand is
// NOT executed; `runPanic` reverts Panic 0x12 because the SELECTED operand runs).
// The Forge lane pins the same behaviour on real solc/EVM.
contract ShortCircuitPureOperandTarget {
    uint256 private _counter;

    function counter() external view returns (uint256) {
        return _counter;
    }

    function hTrue() internal pure returns (bool) {
        return true;
    }

    function hFalse() internal pure returns (bool) {
        return false;
    }

    function jZero() internal pure returns (uint256) {
        return 0;
    }

    function jBump() internal returns (uint256) {
        _counter += 1;
        return 5;
    }

    // true && (5+1 > 0) = true.
    function pureOperand() external pure returns (bool) {
        return hTrue() && (jZero() + 6 > 0);
    }

    // lhs false => `(jBump()+1 > 0)` skipped: jBump() not called, counter 0.
    function skipEffect() external returns (bool) {
        return hFalse() && (jBump() + 1 > 0);
    }

    // lhs true => `(jBump()+1 > 0)` runs: counter 1.
    function runEffect() external returns (bool) {
        return hTrue() && (jBump() + 1 > 0);
    }

    // lhs false => `(1/jZero() > 0)` skipped: NO Panic, returns false.
    function skipPanic() external pure returns (bool) {
        return hFalse() && (uint256(1) / jZero() > 0);
    }

    // lhs true (via ||) => `(1/jZero() > 0)` skipped: NO Panic, returns true.
    function skipPanicOr() external pure returns (bool) {
        return hTrue() || (uint256(1) / jZero() > 0);
    }

    // lhs true => `(1/jZero() > 0)` SELECTED: Panic 0x12 (div by zero).
    function runPanic() external pure returns (bool) {
        return hTrue() && (uint256(1) / jZero() > 0);
    }
}
