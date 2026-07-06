// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StringIndex {
    function bad(string calldata input)
        external
        pure
        returns (bytes1)
    {
        return input[0];
    }
}
