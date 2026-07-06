// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
pragma abicoder v1;

contract V1NestedDynamicArray {
    function use(uint256[][] memory values)
        external
        pure
        returns (uint256)
    {
        return values.length;
    }
}
