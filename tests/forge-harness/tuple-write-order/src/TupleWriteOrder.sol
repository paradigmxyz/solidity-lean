// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// #132 TUPLE-WRITE-ORDER — for a tuple assignment `(lhs0, lhs1, ...) = rhs`,
// solc (1) evaluates the RHS fully into temporaries, (2) computes ALL LHS
// lvalue references up front, LEFT-TO-RIGHT (visiting the LHS TupleExpression
// resolves every component's lvalue before any store), then (3) performs the
// stores RIGHT-TO-LEFT ("assign from right to left to optimize stack layout").
//
// Two observable consequences pinned here:
//  * When two LHS components ALIAS the same location, the LEFTMOST assignment
//    wins (right-to-left stores mean the leftmost is written last).
//  * A later component's index/key expression observes PRE-STORE state (all
//    lvalue refs are resolved before any write).
//
// solidity-lean formerly recursed head-first and interleaved resolve-then-write
// per component, so (a) the rightmost aliased write won and (b) a later
// component's index observed earlier components' writes. Both are fixed by
// resolving all LHS refs left-to-right, then storing right-to-left.
contract TupleWriteOrderHarnessTarget {
    uint256[6] arr;

    // Repro 1: two aliased LOCAL targets. Leftmost wins → x == 1.
    function runLocalAlias() external pure returns (uint256) {
        uint256 x;
        (x, x) = (1, 2);
        return x; // 1
    }

    // Repro 2: two aliased STORAGE-INDEX targets. Leftmost wins → arr[0] == 1.
    function runStorageAlias() external returns (uint256) {
        (arr[0], arr[0]) = (1, 2);
        return arr[0]; // 1
    }

    // Repro 3: the second LHS index `arr[arr[0]]` observes PRE-STORE arr[0]==5,
    // so it resolves to arr[5] (not arr[1]). Stores run right-to-left: arr[5]=2
    // first, then arr[0]=1. Result: arr[0]==1, arr[1]==0, arr[5]==2.
    // Packed as arr[0]*100 + arr[1]*10 + arr[5] == 102.
    function runIndexPreStore() external returns (uint256) {
        arr[0] = 5;
        (arr[0], arr[arr[0]]) = (1, 2);
        return arr[0] * 100 + arr[1] * 10 + arr[5]; // 102
    }

    // Reader used to confirm individual stored slots on both sides.
    function getArr(uint256 i) external view returns (uint256) { return arr[i]; }
}
