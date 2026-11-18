// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract OwnedCtor {
    uint256 x;
    address owner;
    address deployer;

    constructor(uint256 x0, address owner0) {
        require(x0 != 0);
        x = x0;
        owner = owner0;
        deployer = msg.sender;
    }

    function get() external view returns (uint256) {
        if (msg.sender == owner) {
            return x;
        }
        return 0;
    }
}
