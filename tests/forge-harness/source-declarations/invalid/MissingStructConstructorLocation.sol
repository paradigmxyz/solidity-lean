// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MissingStructConstructorLocation {
    struct Point {
        uint256 x;
    }

    uint256 public x;

    constructor(Point point) {
        x = point.x;
    }
}
