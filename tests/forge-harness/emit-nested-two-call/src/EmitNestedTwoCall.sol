// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract EmitNestedTwoCallHarnessTarget {
    event N2(uint256[][] m, uint256 k);

    function mk() internal pure returns (uint256[][] memory m) {
        m = new uint256[][](1);
        m[0] = new uint256[](1);
        m[0][0] = 4;
    }

    function f2() internal pure returns (uint256) {
        return 9;
    }

    function go() external {
        emit N2(mk(), f2());
    }
}
