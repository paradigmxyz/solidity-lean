// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PackedNestedArray {
    function bad(uint256[][] memory values)
        external
        pure
        returns (bytes memory)
    {
        return abi.encodePacked(values);
    }
}
