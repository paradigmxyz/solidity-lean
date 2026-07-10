// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #135 ARRAY-MUTATION-VS-USINGFOR pin: builtin `push`/`pop` exist ONLY on
// STORAGE dynamic arrays. On a MEMORY (or calldata) array the builtin does not
// exist, so a member call `m.pop()` / `m.push(v)` must resolve through
// using-for to the attached library function — solc lowers `m.pop()` to
// `MemArrLib.pop(m)`. solidity-lean formerly intercepted the name `push`/`pop`
// for ANY array receiver and demanded a storage lvalue, over-rejecting these.
library MemArrLib {
    // Attached `pop` on a memory array: NOT the builtin (which mutates storage).
    function pop(uint256[] memory s) internal pure returns (uint256) {
        return s.length;
    }

    // Attached `push` on a memory array with an extra arg.
    function push(uint256[] memory s, uint256 v) internal pure returns (uint256) {
        return s.length + v;
    }
}

using MemArrLib for uint256[];

contract ArrayMutationUsingForHarnessTarget {
    // memory receiver -> MemArrLib.pop(m) == length == 3
    function viaMemoryPop() public pure returns (uint256) {
        uint256[] memory m = new uint256[](3);
        return m.pop();
    }

    // memory receiver -> MemArrLib.push(m, 5) == length + 5 == 2 + 5 == 7
    function viaMemoryPush() public pure returns (uint256) {
        uint256[] memory m = new uint256[](2);
        return m.push(5);
    }

    // calldata receiver -> MemArrLib.pop(c) == length
    function viaCalldataPop(uint256[] calldata c) public pure returns (uint256) {
        return c.pop();
    }
}
