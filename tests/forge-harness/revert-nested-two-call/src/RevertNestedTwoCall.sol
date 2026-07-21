// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract RevertNestedTwoCallHarnessTarget {
    error Nested(uint256[][] a, string b);

    function mk() internal pure returns (uint256[][] memory m) {
        m = new uint256[][](1);
        m[0] = new uint256[](1);
        m[0][0] = 4;
    }

    function sk() internal pure returns (string memory) {
        return "qq";
    }

    function go() external pure {
        revert Nested(mk(), sk());
    }
}
