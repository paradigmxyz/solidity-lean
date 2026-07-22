// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Register v1.3 (X-RETABI retired): array return types ARE in the comparable
// subset — the recursive ABI codec renders `T[]` exactly as Solidus's `[..]`.
// Both engines must render success|[w:7,w:8,w:9] -> NO_DIVERGENCE.
contract ArrRet {
    function vals() external pure returns (uint256[] memory) {
        uint256[] memory a = new uint256[](3);
        a[0] = 7; a[1] = 8; a[2] = 9;
        return a;
    }
}
