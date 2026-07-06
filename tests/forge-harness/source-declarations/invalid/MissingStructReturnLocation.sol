// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MissingStructReturnLocation {
    struct Point {
        uint256 x;
    }

    function makePoint() external pure returns (Point) {
        return Point(1);
    }
}
