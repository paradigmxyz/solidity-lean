// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #135 ARRAY-MUTATION-VS-USINGFOR (Div2, over-accept). A storage dynamic array
// has the builtin `push`; an attached (using-for) `push` of the same name lives
// in the SAME member namespace, so `arr.push(7)` is AMBIGUOUS. Pinned solc
// rejects: `Member "push" not unique after argument-dependent lookup`. The
// model's over-accept witness (amUfAmbiguousStoragePushRejected) mirrors this.
library L {
    function push(uint256[] storage s, uint256 v) internal {
        s[0] = v;
    }
}

using L for uint256[];

contract C {
    uint256[] arr;

    function g() public {
        arr.push(7);
    }
}
