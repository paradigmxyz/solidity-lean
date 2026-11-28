// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main {
    bytes1 constant X = bytes1(uint8(255) + uint8(1));
    function f(bool b) external pure returns (uint256) {
        if (b) return X.length;
        return 3;
    }
}
