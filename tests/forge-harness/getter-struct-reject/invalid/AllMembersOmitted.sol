// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #63 (GET-STRUCT) solc error 5359: every direct member of the gettered struct
// is omitted (a mapping and a dynamic array), so the getter would return no
// values.
//   Error: The struct has all its members omitted, therefore the getter cannot
//          return any values.
contract C {
    struct S {
        mapping(uint256 => uint256) m;
        uint256[] arr;
    }

    S public s;
}
