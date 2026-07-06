// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract TupleDestructureHarnessTarget {
    function pair(uint256 x) internal pure returns (uint256, uint256) {
        return (x + 1, x + 2);
    }

    function directPair(uint256 x) external pure returns (uint256, uint256) {
        return (x + 3, x + 4);
    }

    function destructureCall(uint256 x) external pure returns (uint256) {
        (uint256 left, uint256 right) = pair(x);
        return left * 10 + right;
    }

    function literalHole(uint256 x) external pure returns (uint256) {
        (uint256 left, , uint256 right) = (x, x + 1, x + 2);
        return left * 100 + right;
    }

    function swap(uint256 x) external pure returns (uint256) {
        uint256 left = x;
        uint256 right = x + 1;
        (left, right) = (right, left);
        return left * 10 + right;
    }
}
