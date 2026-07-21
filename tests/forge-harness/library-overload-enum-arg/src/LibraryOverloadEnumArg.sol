// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

library L {
    enum E { A, B }

    // Same-arity overload pair: an enum-typed argument must bind f(E), never
    // f(uint8) (no implicit enum<->uint conversion in Solidity).
    function f(uint8) internal pure returns (uint256) {
        return 1;
    }

    function f(E) internal pure returns (uint256) {
        return 2;
    }

    // Single-candidate coverage control (decf368's shape): an explicit
    // enum-conversion argument to the only candidate must still rewrite.
    function isOff(E m) internal pure returns (bool) {
        return m == E.A;
    }

    // Correctly-typed two-argument overload pair.
    function g(uint256 a, uint8 b) internal pure returns (uint256) {
        return a + b;
    }

    function g(uint256 a, E e) internal pure returns (uint256) {
        return a * 100 + uint256(uint8(e));
    }
}

contract LibraryOverloadEnumArgHarnessTarget {
    using L for *;

    // Enum member literal argument: binds f(E) => 2.
    function enumLiteralOverload() external pure returns (uint256) {
        return L.f(L.E.B);
    }

    // uint8 argument: binds f(uint8) => 1.
    function uintOverload(uint8 v) external pure returns (uint256) {
        return L.f(v);
    }

    // Explicit enum conversion argument: binds f(E) => 2.
    function convOverload(uint8 m) external pure returns (uint256) {
        return L.f(L.E(m));
    }

    // decf368 coverage control: single candidate, explicit enum conversion.
    function singleCandidate(uint8 m) external pure returns (bool) {
        return L.isOff(L.E(m));
    }

    // Two-arg overloads bind by the second argument's type.
    function twoArgUint(uint256 a, uint8 b) external pure returns (uint256) {
        return L.g(a, b);
    }

    function twoArgEnum(uint256 a) external pure returns (uint256) {
        return L.g(a, L.E.B);
    }
}
