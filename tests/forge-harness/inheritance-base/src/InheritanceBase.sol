// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract InheritanceBaseHarnessBase {
    uint256 internal baseValue;

    constructor(uint256 seed) {
        baseValue = seed + 1;
    }

    function readBase() external view returns (uint256) {
        return baseValue;
    }
}

contract InheritanceBaseHarnessTarget is InheritanceBaseHarnessBase {
    uint256 private own;

    constructor(uint256 seed) InheritanceBaseHarnessBase(seed + 2) {
        own = baseValue + 3;
    }

    function readOwn() external view returns (uint256) {
        return own;
    }
}
