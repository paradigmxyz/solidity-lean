// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StorageToCalldataReturn {
    uint256[] private stored;

    function bad() public view returns (uint256[] calldata) {
        return stored;
    }
}
