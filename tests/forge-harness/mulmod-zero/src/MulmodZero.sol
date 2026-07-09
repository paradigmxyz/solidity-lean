// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// MULMOD0 accepted controls. A NON-constant modulus (`runtimeMulmod`) is
// accepted by solc and by solidity-lean; a runtime zero modulus is a runtime
// Panic 0x12, NOT a compile error. A constant NON-zero modulus (`constNonzero`)
// is likewise accepted and folds at runtime. The paired constant-ZERO modulus
// programs that solc REJECTS at compile time live under `invalid/`.
contract MulmodZeroHarnessTarget {
    // Non-constant modulus: compiles; `m == 0` panics 0x12 at runtime.
    function runtimeMulmod(uint256 m) public pure returns (uint256) {
        return mulmod(2, 3, m);
    }

    function runtimeAddmod(uint256 m) public pure returns (uint256) {
        return addmod(2, 3, m);
    }

    // Constant non-zero modulus: accepted; mulmod(2,3,7) = 6, addmod(2,3,7) = 5.
    function constNonzeroMul() public pure returns (uint256) {
        return mulmod(2, 3, 7);
    }

    function constNonzeroAdd() public pure returns (uint256) {
        return addmod(2, 3, 7);
    }
}
