// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

abstract contract ConstructorCalldataParam {
    struct Point {
        uint256 x;
    }

    constructor(Point calldata point) {
        point;
    }
}
