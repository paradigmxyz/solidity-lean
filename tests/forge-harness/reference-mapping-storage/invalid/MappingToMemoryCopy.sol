// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MappingToMemoryCopy {
    mapping(uint256 => uint256) private values;

    function bad() external view {
        mapping(uint256 => uint256) storage local = values;
        mapping(uint256 => uint256) memory copied = local;
        copied;
    }
}
