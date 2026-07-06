// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract LoopControlHarnessTarget {
    function whileSum(uint256 limit) external pure returns (uint256) {
        uint256 i = 0;
        uint256 acc = 0;

        while (i < limit) {
            i += 1;

            if (i == 3) {
                continue;
            }

            if (i == 6) {
                break;
            }

            acc += i;
        }

        return acc;
    }

    function forSum(uint256 limit) external pure returns (uint256) {
        uint256 acc = 0;

        for (uint256 i = 0; i < limit; i += 1) {
            if (i == 3) {
                continue;
            }

            if (i == 6) {
                break;
            }

            acc += i;
        }

        return acc;
    }
}
