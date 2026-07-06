// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract FunctionTypeLocations {
    uint256[] private stored;

    function memoryTarget(uint256[] memory values)
        internal
        pure
        returns (uint256[] memory)
    {
        values[0] += 1;
        return values;
    }

    function calldataTarget(uint256[] calldata values)
        internal
        pure
        returns (uint256[] calldata)
    {
        return values;
    }

    function storageTarget(uint256[] storage values)
        internal
        returns (uint256[] storage)
    {
        values[0] += 1;
        return values;
    }

    function runMemory(uint256[] memory values)
        external
        pure
        returns (uint256, uint256)
    {
        function(uint256[] memory) internal pure returns (uint256[] memory) fn =
            memoryTarget;
        uint256[] memory result = fn(values);
        return (values[0], result[0]);
    }

    function runCalldata(uint256[] calldata values)
        external
        pure
        returns (uint256, uint256)
    {
        function(uint256[] calldata) internal pure returns (uint256[] calldata) fn =
            calldataTarget;
        uint256[] calldata result = fn(values);
        return (values[0], result.length);
    }

    function runStorage() external returns (uint256, uint256) {
        if (stored.length == 0) {
            stored.push(7);
        }
        function(uint256[] storage) internal returns (uint256[] storage) fn =
            storageTarget;
        uint256[] storage result = fn(stored);
        return (stored[0], result[0]);
    }
}
