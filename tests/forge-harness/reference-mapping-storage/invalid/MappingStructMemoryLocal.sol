// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MappingStructMemoryLocal {
    struct Ledger {
        uint256 total;
        mapping(uint256 => uint256) credits;
    }

    function bad() external pure {
        Ledger memory local;
        local;
    }
}
