// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PureStorageProjection {
    function readLength(uint256[] storage values)
        internal
        pure
        returns (uint256)
    {
        return values.length;
    }
}
