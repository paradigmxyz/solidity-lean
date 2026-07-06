// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ExpressionPrimitivesHarnessTarget {
    uint256 public value;

    function update(uint256 x) external returns (uint256) {
        uint256 a = x;
        a++;
        ++a;
        a--;
        --a;
        value = a;
        delete value;
        return value + a;
    }

    function unary(
        bool flag,
        int256 signedValue
    ) external pure returns (bool, int256, uint256) {
        return (!flag, -signedValue, ~uint256(0));
    }

    function arrayPick() external pure returns (uint256) {
        uint256[3] memory xs = [uint256(1), 2, 3];
        return xs[1];
    }

    function modularArithmetic()
        external
        pure
        returns (uint256 sumMod, uint256 productMod, bytes32 digest)
    {
        sumMod = addmod(type(uint256).max, 2, 5);
        productMod = mulmod(type(uint256).max, type(uint256).max, 10);
        digest = keccak256(hex"010203");
    }

    function addmodZero(uint256 modulus) external pure returns (uint256) {
        return addmod(1, 2, modulus);
    }

    function mulmodZero(uint256 modulus) external pure returns (uint256) {
        return mulmod(1, 2, modulus);
    }
}
