// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract SignedArraySliceIndex {
    function bad(uint256[] calldata input, int256 offset)
        external
        pure
        returns (uint256[] memory)
    {
        return input[offset:2];
    }
}
