// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StorageToCalldataCall {
    uint256[] private stored;

    function helper(uint256[] calldata input)
        internal
        pure
        returns (uint256)
    {
        return input.length;
    }

    function bad() public view returns (uint256) {
        return helper(stored);
    }
}
