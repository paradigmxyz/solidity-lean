// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ConstructorStorageParamConcrete {
    struct Point {
        uint256 x;
    }

    constructor(Point storage point) {
        point;
    }
}
