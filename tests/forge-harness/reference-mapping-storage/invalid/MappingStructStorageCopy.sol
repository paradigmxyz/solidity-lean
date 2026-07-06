// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MappingStructStorageCopy {
    struct Ledger {
        uint256 total;
        mapping(uint256 => uint256) credits;
    }

    Ledger private first;
    Ledger private second;

    function bad() external {
        first = second;
    }
}
