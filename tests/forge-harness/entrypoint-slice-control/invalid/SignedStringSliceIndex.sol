// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract SignedStringSliceIndex {
    function bad(string calldata payload, int256 offset)
        external
        pure
        returns (string memory)
    {
        return payload[offset:4];
    }
}
