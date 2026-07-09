// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// ALLOWED-CHEATCODE case (review P0 #3). The test pins block.timestamp via
// vm.warp(12345). That override is MIRRORED into the solidity-lean env, so both
// engines see timestamp=12345 -> NO_DIVERGENCE.
contract CA {
    function ts() external view returns (uint256) { return block.timestamp; }
}
