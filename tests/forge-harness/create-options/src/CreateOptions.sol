// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract CreatedWithOptions {
    uint256 private value;

    constructor(uint256 seed) payable {
        value = seed + msg.value;
    }

    function read() external view returns (uint256) {
        return value;
    }
}

contract CreateOptionsFactory {
    function make(uint256 seed, uint256 payment, bytes32 salt)
        external
        payable
        returns (CreatedWithOptions)
    {
        return new CreatedWithOptions{value: payment, salt: salt}(seed);
    }
}
