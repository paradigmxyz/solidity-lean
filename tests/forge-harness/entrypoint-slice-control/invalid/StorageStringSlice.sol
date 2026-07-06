// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StorageStringSlice {
    string private stored;

    function bad() external view returns (string memory) {
        return stored[1:2];
    }
}
