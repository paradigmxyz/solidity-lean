// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Created {
    constructor(uint256 seed) payable {}
}

contract DuplicateSaltOption {
    function make(uint256 seed, bytes32 salt) external returns (Created) {
        return new Created{salt: salt, salt: salt}(seed);
    }
}
