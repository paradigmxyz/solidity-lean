// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// A constant EXPRESSION modulus that folds to zero (`1 - 1`) must also be caught
// by the constant evaluator — Error 4195 "Arithmetic modulo zero" (MULMOD0).
contract MulmodConstExprZero {
    function f() public pure returns (uint256) {
        return mulmod(2, 3, 1 - 1);
    }
}
