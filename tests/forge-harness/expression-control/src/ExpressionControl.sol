// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract ExpressionControlHarnessTarget {
    function shortCircuit() external pure returns (uint256) {
        uint256 x = 0;

        if (false && ((x = 1) == 1)) {
            x += 10000;
        }

        if (true || ((x = 2) == 2)) {
            x += 10;
        }

        if (true && ((x = x + 3) > 0)) {
            x += 100;
        }

        if (false || ((x = x + 5) > 0)) {
            x += 1000;
        }

        return x;
    }

    function ternarySelect(bool flag) external pure returns (uint256) {
        uint256 x = 1;
        uint256 y = flag ? (x = 7) : (x = 9);
        return x * 100 + y;
    }
}
