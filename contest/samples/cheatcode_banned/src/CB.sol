// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// BANNED-CHEATCODE ATTACK (review P0 #3). The TEST uses vm.store to forge
// storage the entry then reads back, manufacturing a divergence Solidus (run
// from a clean env) can never reproduce. The cheatcode gate must REJECT it.
contract CB {
    uint256 public x;
    function run() external view returns (uint256) { return x; }
}
