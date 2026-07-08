// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/BlockEnvBuiltins.sol";

interface Vm {
    function roll(uint256) external;
}

// Ground-truth pinning for BLOCKHASH (blockhash(uint)) and BLOBHASH
// (blobhash(uint), EIP-4844). vm.roll fixes block.number = 1000 so Foundry's
// blockhash of recent blocks is deterministic across runs (verified stable).
// The availability window is the most recent 256 blocks (number-256 ..=
// number-1); the current block, future blocks, and blocks older than 256 return
// 0. blobhash returns 0 for every index in Foundry's default non-blob tx.
contract BlockEnvBuiltinsForgeTest {
    Vm constant vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    function testBlockhashWindow() public {
        BlockEnvBuiltinsHarnessTarget t = new BlockEnvBuiltinsHarnessTarget();
        vm.roll(1000);

        require(t.blockHashOf(1000) == bytes32(0), "current -> 0");
        require(
            t.blockHashOf(999) ==
                0xf0222e4555f079f2fdbf570707db75ee508caa46321baeff622a993218303d10,
            "recent (number-1)"
        );
        require(
            t.blockHashOf(744) ==
                0x7468eddb0720a03646876d25045fa535478c57a57b912a197efd90e8d667279c,
            "boundary (number-256)"
        );
        require(t.blockHashOf(743) == bytes32(0), "too old (number-257) -> 0");
        require(t.blockHashOf(1001) == bytes32(0), "future -> 0");
    }

    function testBlobhashZero() public {
        BlockEnvBuiltinsHarnessTarget t = new BlockEnvBuiltinsHarnessTarget();

        require(t.blobHashOf(0) == bytes32(0), "blobhash(0) -> 0");
        require(t.blobHashOf(1) == bytes32(0), "blobhash(1) -> 0");
    }
}
