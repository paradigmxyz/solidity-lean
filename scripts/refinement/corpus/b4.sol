// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main {
    struct S { uint8 x; }
    function make(uint8 a) internal pure returns (S memory) { return S(a + 1); }
    function f(uint8 a) external pure returns (uint8) {
        unchecked { return make(a).x; }
    }
}
