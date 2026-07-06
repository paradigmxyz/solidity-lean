// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MappingIndexHarnessTarget {
    mapping(uint256 => uint256) public values;
    mapping(address => uint256) public balances;

    function writeRead(
        uint256 key,
        uint256 value
    ) external returns (uint256) {
        values[key] = value;
        return values[key];
    }

    function readDefault(uint256 key) external view returns (uint256) {
        return values[key];
    }

    function writeTwo(
        uint256 firstKey,
        uint256 secondKey
    ) external returns (uint256) {
        values[firstKey] = 11;
        values[secondKey] = 22;
        return values[firstKey] + values[secondKey];
    }

    function writeAddress(
        address who,
        uint256 value
    ) external returns (uint256) {
        balances[who] = value;
        return balances[who];
    }
}
