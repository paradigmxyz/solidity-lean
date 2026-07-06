// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StorageToCalldataReassignment {
    uint256[] private stored;

    function bad(uint256[] calldata input) public view returns (uint256) {
        uint256[] calldata local = input;
        local = stored;
        return local.length;
    }
}
