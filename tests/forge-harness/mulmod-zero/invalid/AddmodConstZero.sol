// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// A compile-time-CONSTANT zero modulus in addmod is Error 4195 "Arithmetic
// modulo zero" in solc's constant evaluator — a COMPILE error (MULMOD0).
contract AddmodConstZero {
    function f() public pure returns (uint256) {
        return addmod(2, 3, 0);
    }
}
