// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MappingMemoryLocal {
    function bad() external pure {
        mapping(uint256 => uint256) memory local;
        local;
    }
}
