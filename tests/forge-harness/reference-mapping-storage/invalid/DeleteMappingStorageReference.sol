// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract DeleteMappingStorageReference {
    mapping(uint256 => uint256) private values;

    function bad() external {
        mapping(uint256 => uint256) storage local = values;
        delete local;
    }
}
