// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Boundary-completion arc, stage E: recursion through REFERENCE signatures —
// the residual slice of the recursion gap the function-boundary refactor left
// open (value signatures landed first). solc accepts and runs all of these;
// under the splice era they were silently rejected (toCoreContract? = none).
contract RecursionRefSignaturesHarnessTarget {
    struct Node {
        uint256 value;
        uint256 next; // index into nodes; 0 = end (node 0 is a sentinel)
    }

    mapping(uint256 => Node) private nodes;

    // Recursive linked-list walk over a MAPPING through a storage-ref param.
    function sumList(Node storage node) internal view returns (uint256) {
        if (node.next == 0) {
            return node.value;
        }
        return node.value + sumList(nodes[node.next]);
    }

    // Build 1 -> 2 -> 3 with values 10, 20, 30; walk from node 1 -> 60.
    function viaStorageRecursion() public returns (uint256) {
        nodes[1] = Node(10, 2);
        nodes[2] = Node(20, 3);
        nodes[3] = Node(30, 0);
        return sumList(nodes[1]);
    }

    // Recursive sum over a MEMORY array param (pointer pass-through).
    function sumMemory(uint256[] memory xs, uint256 i)
        internal
        pure
        returns (uint256)
    {
        if (i >= xs.length) {
            return 0;
        }
        return xs[i] + sumMemory(xs, i + 1);
    }

    // Also asserts aliasing: the recursion's mutation through the pointer is
    // visible to the caller. [7, 8] -> sum 15, then xs[0] = 99 inside the
    // callee chain -> caller reads 99. Encoded 15 * 1000 + 99 = 15099.
    function mutateFirst(uint256[] memory xs, uint256 depth) internal pure {
        if (depth == 0) {
            xs[0] = 99;
            return;
        }
        mutateFirst(xs, depth - 1);
    }

    function viaMemoryRecursion() public pure returns (uint256) {
        uint256[] memory xs = new uint256[](2);
        xs[0] = 7;
        xs[1] = 8;
        uint256 s = sumMemory(xs, 0);
        mutateFirst(xs, 3);
        return s * 1000 + xs[0]; // 15099
    }
}
