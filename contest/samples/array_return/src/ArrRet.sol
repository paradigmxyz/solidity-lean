// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Array return types are outside the faithfully-comparable ABI subset (X-RETABI):
// the EVM decoder does not yet render `T[]` as Solidus's `[..]`, so comparing
// would raise a spurious divergence. Must be REJECTED_OOS, not scored.
contract ArrRet {
    function vals() external pure returns (uint256[] memory) {
        uint256[] memory a = new uint256[](3);
        a[0] = 7; a[1] = 8; a[2] = 9;
        return a;
    }
}
