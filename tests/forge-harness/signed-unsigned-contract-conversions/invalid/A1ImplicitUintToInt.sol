// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A1: solc IntegerType::isImplicitlyConvertibleTo (Types.cpp:611-614) forbids
// ALL implicit signed<->unsigned conversions. uint8 is NOT implicitly
// convertible to int16.
// Pinned solc 0.8.35 rejects: "Type uint8 is not implicitly convertible to
// expected type int16."
contract A1ImplicitUintToInt {
    function f(uint8 a) public pure returns (int16) {
        return a;
    }
}
