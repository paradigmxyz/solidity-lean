// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Created {
    constructor(uint256 seed) payable {}
}

contract BadSaltType {
    function make(uint256 seed) external returns (Created) {
        return new Created{salt: 1}(seed);
    }
}
