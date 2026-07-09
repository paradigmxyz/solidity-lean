// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// solc 0.8.35 rejects ordered comparison across DIFFERENT enum types
// (TypeError 2271: "Built-in binary operator < cannot be applied to types
// enum A and enum B"). Same-enum ordered comparison is accepted; this pins
// that the fix keeps distinct enums rejected.
contract DifferentEnumCompare {
    enum A { X, Y }
    enum B { P, Q }

    function bad() external pure returns (bool) {
        return A.X < B.Q;
    }
}
