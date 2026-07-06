// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ModifierMissingStructParamLocation {
    struct Point {
        uint256 x;
    }

    modifier withPoint(Point point) {
        _;
    }
}
