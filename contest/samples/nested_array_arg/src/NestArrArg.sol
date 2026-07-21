// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Register v1.4: a NESTED dynamic array `uint256[][]` ENTRY PARAMETER —
// head/tail offsets within offsets — encodes end-to-end on both engines.
contract NestArrArg {
    function pick(uint256[][] memory m) external pure returns (uint256, uint256) {
        // m = [[1,2],[3]] -> m[1][0] + m[0][1] = 3 + 2 = 5; outer length 2.
        return (m[1][0] + m[0][1], m.length);
    }
}
