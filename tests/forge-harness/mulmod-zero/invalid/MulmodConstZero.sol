// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// A compile-time-CONSTANT zero modulus in mulmod is Error 4195 "Arithmetic
// modulo zero" in solc's constant evaluator — a COMPILE error, not a runtime
// Panic. solidity-lean must mirror this (MULMOD0).
contract MulmodConstZero {
    function f() public pure returns (uint256) {
        return mulmod(2, 3, 0);
    }
}
