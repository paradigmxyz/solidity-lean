// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract ModifierOrderHarnessTarget {
    uint256 private value;

    modifier add(uint256 beforeValue, uint256 afterValue) {
        value += beforeValue;
        _;
        value += afterValue;
    }

    modifier gate(uint256 limit) {
        require(value < limit, "gate");
        _;
    }

    function run(uint256 x)
        external
        add(1, 100)
        gate(10)
    {
        value += x;
    }

    function blocked()
        external
        add(20, 1)
        gate(10)
    {
        value += 1;
    }

    function read() external view returns (uint256) {
        return value;
    }
}
