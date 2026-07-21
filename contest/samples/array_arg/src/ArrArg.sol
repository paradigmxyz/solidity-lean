// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Register v1.4 (X-ARGVAL retired): a `uint256[]` ENTRY PARAMETER is encoded
// end-to-end — the JSON-list claim arg [7,8,9] becomes type-directed ABI
// calldata on the EVM side and Value.dynamicArray on the Lean side — so both
// engines receive the same logical call and render success|w:24,w:3.
contract ArrArg {
    function sum(uint256[] memory xs) external pure returns (uint256, uint256) {
        uint256 s;
        for (uint256 i = 0; i < xs.length; i++) {
            s += xs[i];
        }
        return (s, xs.length);
    }
}
