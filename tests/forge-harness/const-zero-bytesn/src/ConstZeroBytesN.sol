// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// #121 CONST-ZERO-BYTESN: any constant expression that FOLDS to 0 is
// implicitly convertible to any bytesN (solc RationalNumberType, the
// `m_value == rational(0)` branch on the folded value). The folded 0 lowers to
// the zero word regardless of width; a nonzero fold does NOT convert.
contract ConstZeroBytesN {
    // `1 - 1` folds to 0 -> convertible to bytes32; runtime value bytes32(0).
    function zeroFold() external pure returns (bytes32) {
        bytes32 x = 1 - 1;
        return x;
    }

    // `2 * 0` folds to 0 -> convertible to bytes16; runtime value bytes16(0).
    function zeroFold16() external pure returns (bytes16) {
        bytes16 y = 2 * 0;
        return y;
    }

    // A single bytes32 overload target for the folded-zero argument call below.
    function g(bytes32) public pure returns (uint256) {
        return 42;
    }

    // `g(2 - 2)`: the folded 0 argument converts to bytes32, resolving g.
    function callGWithZeroFold() external pure returns (uint256) {
        return g(2 - 2);
    }
}
