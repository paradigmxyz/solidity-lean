// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StorageBytesSlice {
    bytes private stored;

    function bad() external view returns (bytes memory) {
        return stored[1:2];
    }
}
