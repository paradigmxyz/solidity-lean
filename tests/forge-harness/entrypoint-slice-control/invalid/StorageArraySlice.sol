// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StorageArraySlice {
    uint256[] private stored;

    function bad() external view returns (uint256[] memory) {
        return stored[1:2];
    }
}
