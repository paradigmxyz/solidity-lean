// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// solc REJECTS: a bare literal index carries a rational-literal type, so the
// compile-time constant out-of-bounds check fires (TypeError 3383). Contrast
// the accepted `a[uint256(5)]` in ../src/ArrayBounds.sol.
contract BareLiteralOob {
    uint256[3] a;

    function f() external view returns (uint256) {
        return a[5];
    }
}
