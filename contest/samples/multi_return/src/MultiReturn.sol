// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Mixed-scalar multi-return: a signed int, a sub-256 uint, an address, and a
// bytesN in ONE tuple return — the combination most likely to expose a per-type
// rendering asymmetry between the EVM ABI decode and the solidity-lean renderer
// (differential probe; no single existing sample covers all four together).
contract MultiReturn {
    function f() external pure returns (int256, uint128, address, bytes4) {
        return (-7, 42, address(0x0000000000000000000000000000000000001234), 0xAABBCCDD);
    }
}
