// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// G13 — a NESTED tuple on the assignment LHS (`((a, b), c) = …`). solc accepts
// these; the RHS tuple is evaluated once, left-to-right, into temps and then
// destructured against the nested target tree in lockstep. A hole still
// evaluates its RHS component and discards it.
contract NestedTupleAssignmentHarnessTarget {
    function nestedLit(uint256 x) external pure returns (uint256) {
        uint256 a;
        uint256 b;
        uint256 c;
        ((a, b), c) = ((x, x + 1), x + 2);
        return a * 100 + b * 10 + c;
    }

    function nestedRight(uint256 x) external pure returns (uint256) {
        uint256 a;
        uint256 b;
        uint256 c;
        (a, (b, c)) = (x, (x + 1, x + 2));
        return a * 100 + b * 10 + c;
    }

    // The RHS is read into temps BEFORE any assignment, so this swaps.
    function nestedSwap(uint256 x) external pure returns (uint256) {
        uint256 a = x;
        uint256 b = x + 1;
        uint256 c = x + 2;
        ((a, b), c) = ((b, c), a);
        return a * 100 + b * 10 + c;
    }

    // A hole in a nested position: its RHS component (x+1) is evaluated then
    // discarded; only a and c are written.
    function nestedHole(uint256 x) external pure returns (uint256) {
        uint256 a;
        uint256 c;
        ((a, ), c) = ((x, x + 1), x + 2);
        return a * 10 + c;
    }
}
