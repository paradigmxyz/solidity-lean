// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// solc REJECTS: "Index range access is only supported for dynamic calldata
// arrays." A fixed-size `uint256[3] calldata` may not be sliced. Contrast the
// accepted dynamic `uint256[] calldata` slice in ../src/ArrayBounds.sol.
contract FixedArraySlice {
    function f(uint256[3] calldata a) external pure returns (uint256) {
        uint256[] calldata s = a[1:2];
        return s.length;
    }
}
