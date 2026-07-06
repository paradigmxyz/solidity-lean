// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MappingStructMemoryReturn {
    struct Ledger {
        uint256 total;
        mapping(uint256 => uint256) credits;
    }

    mapping(uint256 => Ledger) private ledgers;

    function bad(uint256 id) external view returns (Ledger memory) {
        return ledgers[id];
    }
}
