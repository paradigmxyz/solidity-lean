// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Stage-D pin for the boundary-completion arc
// (docs/refs-completion-solc-research.md §3): calldata references cross the
// internal-function boundary as plain (offset, length) descriptor words in
// solc via-IR; calldata is immutable, so a materialized immutable value is
// observationally identical. Covers dynamic array + bytes calldata params,
// a slice-adjusted pair, a calldata ref RETURNED from an internal function,
// and recursion over a calldata array.
contract CalldataRefInternalHarnessTarget {
    function sumAll(uint256[] calldata xs)
        internal
        pure
        returns (uint256 s)
    {
        for (uint256 i = 0; i < xs.length; i++) {
            s += xs[i];
        }
    }

    function firstByte(bytes calldata b) internal pure returns (uint256) {
        return uint256(uint8(b[0]));
    }

    function pickTail(bytes calldata b)
        internal
        pure
        returns (bytes calldata)
    {
        return b[1:];
    }

    function sumFrom(uint256[] calldata xs, uint256 i)
        internal
        pure
        returns (uint256)
    {
        if (i >= xs.length) {
            return 0;
        }
        return xs[i] + sumFrom(xs, i + 1);
    }

    // sum + first byte through internal calldata params. [3,4,5], 0x0102 ->
    // 12 * 1000 + 1 = 12001.
    function viaParams(uint256[] calldata xs, bytes calldata b)
        public
        pure
        returns (uint256)
    {
        return sumAll(xs) * 1000 + firstByte(b);
    }

    // Slice through the boundary: tail of 0x0102 is 0x02 -> 2.
    function viaSlice(bytes calldata b) public pure returns (uint256) {
        bytes calldata t = pickTail(b);
        return uint256(uint8(t[0]));
    }

    // RECURSION over a calldata ref param (previously silently rejected):
    // sumFrom([3,4,5], 0) = 12.
    function viaRecursion(uint256[] calldata xs)
        public
        pure
        returns (uint256)
    {
        return sumFrom(xs, 0);
    }
}
