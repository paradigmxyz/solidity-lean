// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #63 (GET-STRUCT) solc error 6744: with SHALLOW omission the nested struct
// `inner` is returned WHOLE, but it transitively contains a mapping, so the
// getter has no valid external interface type.
//   Error: Internal or recursive type is not allowed for public state variables.
contract C {
    struct Inner {
        uint256 a;
        mapping(uint256 => uint256) m;
    }

    struct Outer {
        uint256 x;
        Inner inner;
    }

    Outer public o;
}
