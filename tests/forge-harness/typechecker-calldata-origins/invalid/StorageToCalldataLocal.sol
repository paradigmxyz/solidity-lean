// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StorageToCalldataLocal {
    uint256[] private stored;

    function bad() public view returns (uint256) {
        uint256[] calldata local = stored;
        return local.length;
    }
}
