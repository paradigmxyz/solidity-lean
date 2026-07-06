// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MappingStructCalldataParam {
    struct Ledger {
        uint256 total;
        mapping(uint256 => uint256) credits;
    }

    function bad(Ledger calldata input) external pure returns (uint256) {
        return input.total;
    }
}
