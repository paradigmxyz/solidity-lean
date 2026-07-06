// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
pragma abicoder v1;

contract AbiCoderModesHarnessTarget {
    function lengthPlusFirst(uint256[] memory values)
        external
        pure
        returns (uint256)
    {
        return values.length + values[0];
    }

    function encodeArray(uint256[] memory values)
        external
        pure
        returns (bytes memory)
    {
        return abi.encode(values);
    }
}
