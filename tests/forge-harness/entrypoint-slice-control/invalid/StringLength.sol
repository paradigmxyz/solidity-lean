// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StringLength {
    function bad(string calldata input)
        external
        pure
        returns (uint256)
    {
        return input.length;
    }
}
