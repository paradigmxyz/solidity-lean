// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Acceptance-boundary lane for two array divergences vs pinned solc 0.8.35:
//
//  * ARRAY-OOB-CONV (over-reject fix): solc runs its compile-time constant
//    out-of-bounds index check ONLY when the index carries a *rational-literal*
//    type. A bare literal (`a[5]`) is rational-literal and IS checked (rejected,
//    TypeError 3383 -- see invalid/BareLiteralOob.sol). An explicit conversion
//    `a[uint256(5)]` makes the index a plain uint256, which solc does NOT
//    bounds-check; the OOB read reverts at runtime with Panic(0x32).
//
//  * SLICE-FIXED (over-accept fix): index-range (slice) access is only
//    supported for *dynamic* calldata arrays. A dynamic `uint256[] calldata`
//    slice is accepted (dynSlice below); a fixed-size `uint256[3] calldata`
//    slice is rejected ("Index range access is only supported for dynamic
//    calldata arrays." -- see invalid/FixedArraySlice.sol).
contract ArrayBoundsHarnessTarget {
    uint256[3] private a;

    // ARRAY-OOB-CONV: explicitly converted OOB index is accepted at compile
    // time, reverts Panic(0x32) at runtime.
    function convOob() external view returns (uint256) {
        return a[uint256(5)];
    }

    // Control: an in-bounds converted index returns the element (default 0).
    function convInBounds() external view returns (uint256) {
        return a[uint256(2)];
    }

    // SLICE-FIXED: slicing a DYNAMIC calldata array is accepted; returns the
    // slice length (xs[1:3] has length 2).
    function dynSlice(uint256[] calldata xs) external pure returns (uint256) {
        uint256[] calldata s = xs[1:3];
        return s.length;
    }
}
