// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// PUSH-FIELD-LVALUE — assigning THROUGH the storage reference returned by a
// zero-arg dynamic-array `.push()`. solc accepts `xs.push().a = 7` (struct
// element member) and `ys.push()[1] = 9` (fixed-array element index): the push
// appends a default element, then the member/index write targets that new last
// element's storage slot. solidity-lean formerly over-rejected the whole
// contract because it could not lower an lvalue whose base is a `.push()` call
// (only a direct `xs.push() = v` and an index-over-a-var base were handled).
contract PushFieldLValueHarnessTarget {
    struct S { uint a; uint b; }
    S[] xs;
    uint[3][] ys;

    // struct-element member through push(): xs.push().a = 7
    function structMember() external returns (uint, uint, uint) {
        xs.push().a = 7;
        return (xs.length, xs[0].a, xs[0].b);                 // (1, 7, 0)
    }

    // two pushes; each sets one field; the untouched field of each stays 0.
    function structTwoFields() external returns (uint, uint, uint, uint, uint) {
        xs.push().a = 7;
        xs.push().b = 9;
        return (xs.length, xs[0].a, xs[0].b, xs[1].a, xs[1].b); // (2, 7, 0, 0, 9)
    }

    // fixed-array element index through push(): ys.push()[1] = 9
    function arrayIndex() external returns (uint, uint, uint, uint) {
        ys.push()[1] = 9;
        return (ys.length, ys[0][0], ys[0][1], ys[0][2]);      // (1, 0, 9, 0)
    }
}
