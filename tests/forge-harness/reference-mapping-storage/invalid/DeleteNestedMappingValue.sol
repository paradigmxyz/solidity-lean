// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract DeleteNestedMappingValue {
    mapping(uint256 => mapping(uint256 => uint256)) private values;

    function bad(uint256 key) external {
        delete values[key];
    }
}
