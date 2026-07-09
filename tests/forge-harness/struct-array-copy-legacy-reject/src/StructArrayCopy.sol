// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CP1/#48 ACCEPTED controls. solc 0.8.35 LEGACY codegen accepts each copy below
// into a storage array, and each stays accepted by solidity-lean after the
// struct-element reject was added. The rejected shapes (a memory/calldata array
// of struct into storage) live under ../invalid and are pinned via `solc_rejects`.
//
// The precision guard: the reject fires only when the array's IMMEDIATE element
// is a struct. `string[]`/`uint256[][]` (element not a struct) and `S[][]`
// (element is an array, taking solc's sibling branch that accepts a memory
// source) must all stay accepted.
contract StructArrayCopyHarnessTarget {
    struct S {
        uint256 a;
    }

    string[] private words;
    uint256[][] private grid;
    S[][] private nested; // element is S[] (an array), NOT a struct -> accepted
    S private one;        // top-level struct, NOT an array -> accepted

    // string[] memory -> storage (element is `string`, not a struct)
    function setWords(string[] memory m) public {
        words = m;
    }

    function wordAt(uint256 i) public view returns (string memory) {
        return words[i];
    }

    function wordCount() public view returns (uint256) {
        return words.length;
    }

    // uint256[][] memory -> storage (element is `uint256[]`, not a struct)
    function setGrid(uint256[][] memory m) public {
        grid = m;
    }

    function gridAt(uint256 i, uint256 j) public view returns (uint256) {
        return grid[i][j];
    }

    // S[][] memory -> storage: outer element is an ARRAY (S[]), so solc takes the
    // array-base branch and ACCEPTS a memory source under legacy codegen.
    function setNested(S[][] memory m) public {
        nested = m;
    }

    function nestedAt(uint256 i, uint256 j) public view returns (uint256) {
        return nested[i][j].a;
    }

    // top-level struct: S memory -> S storage (a struct, not an array-of-struct)
    function setOne(S memory m) public {
        one = m;
    }

    function oneValue() public view returns (uint256) {
        return one.a;
    }
}
