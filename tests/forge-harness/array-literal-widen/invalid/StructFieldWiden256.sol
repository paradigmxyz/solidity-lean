// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// struct field is uint256[3]; constructing it from a uint8[3] literal — disallowed.
contract StructFieldWiden256 {
    struct S { uint256[3] a; }
    function f() public pure {
        S memory s = S([1, 2, 3]);
        s;
    }
}
