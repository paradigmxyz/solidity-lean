// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract EmitMemoryNestedHarnessTarget {
    event N(uint256[][] rows);

    function run() external {
        uint256[][] memory rows = new uint256[][](2);
        rows[0] = new uint256[](1);
        rows[0][0] = 7;
        rows[1] = new uint256[](2);
        rows[1][0] = 8;
        rows[1][1] = 9;
        emit N(rows);
    }
}
