// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A2: there is no common type between a signed and an unsigned integer for a
// binary op when neither operand is a literal. uint8 + int16 (both variables)
// is a type error.
// Pinned solc 0.8.35 rejects: "Built-in binary operator + cannot be applied to
// types uint8 and int16."
contract A2MixedSignAdd {
    function f(uint8 a, int16 b) public pure returns (int16) {
        return a + b;
    }
}
