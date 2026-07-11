// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #160 RECURSIVE-STRUCT-MEM-CONSTRUCT — memory-constructing a SELF-REFERENTIAL
// struct. solc 0.8.35 accepts and executes `Node memory n = Node(1, new
// Node[](0)); return n.v;` (a struct whose own dynamic-array member has the
// struct as its element type). The model accepted it in the checker but could
// not lower the memory construction: `Ty.resolveStructs` inlines a struct path
// into its fields to a fixed fuel budget, and for a self-referential struct that
// expansion never terminates, so the constructor-argument cast and the declared
// memory-variable type bottom out at DIFFERENT fuel-residual depths. A raw `==`
// of those two giant expansions then reported a spurious type mismatch and the
// whole contract failed to lower (`toCoreContract? = none`). The fix compares
// the two expansions by nominal struct PATH (stopping at each struct boundary),
// which is fuel-independent.
//
// The isolation ladder is pinned alongside G3 in one contract: a dynamic-array
// member of a value type (H1) and of a DIFFERENT struct (H2) already lowered;
// only the self-reference (G3) triggered the bug. Storage use of the recursive
// struct (G1) and mere declaration (G0) also already worked.
contract RecursiveStructMemConstructHarness {
    struct Node { uint256 v; Node[] kids; }        // self-referential (G3 trigger)
    struct Leaf { uint256 v; }
    struct Box { uint256 v; Leaf[] kids; }         // H2: dyn-array of a DIFFERENT struct
    struct Flat { uint256 v; uint256[] kids; }     // H1: dyn-array of a value type

    Node internal stored;                          // G1: recursive struct in storage

    // G3: memory-construct the self-referential struct with an empty child array.
    function constructRecursive() external pure returns (uint256) {
        Node memory n = Node(1, new Node[](0));
        return n.v;
    }

    // H1: dyn-array member of a value type (already worked; pinned for the ladder).
    function constructFlat() external pure returns (uint256) {
        Flat memory n = Flat(2, new uint256[](0));
        return n.v;
    }

    // H2: dyn-array member of a different struct (already worked; pinned).
    function constructBox() external pure returns (uint256) {
        Box memory n = Box(3, new Leaf[](0));
        return n.v;
    }

    // G1: storage field write on the recursive struct, no memory construction.
    function storageWrite() external returns (uint256) {
        stored.v = 5;
        return stored.v;
    }
}
