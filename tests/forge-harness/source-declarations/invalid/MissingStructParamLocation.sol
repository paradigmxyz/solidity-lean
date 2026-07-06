// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MissingStructParamLocation {
    struct Point {
        uint256 x;
    }

    function usePoint(Point point) external pure returns (uint256) {
        return point.x;
    }
}
