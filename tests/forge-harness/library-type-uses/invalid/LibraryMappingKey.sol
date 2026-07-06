// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library L {}

contract LibraryMappingKey {
    mapping(L => uint256) private values;
}
