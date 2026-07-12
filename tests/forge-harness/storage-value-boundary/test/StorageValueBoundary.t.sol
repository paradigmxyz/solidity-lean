// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {StorageValueBoundaryTarget} from "../src/StorageValueBoundary.sol";

/// Real-EVM ground truth for hash-of-storage-bytes: every expectation below is
/// a hard-pinned constant (cross-checked with `cast keccak` / sha256), so the
/// EVM run itself re-verifies the values the Lean side pins.
contract StorageValueBoundaryForgeTest {
    StorageValueBoundaryTarget t;

    function setUp() public { t = new StorageValueBoundaryTarget(); }

    function testH5() public view {
        require(t.h5() == bytes32(0x6ccdf593017c9d38b36c1cb00572feae81abc15173860a4e0904a6c45d3b086e), "h5");
    }
    function testH31() public view {
        require(t.h31() == bytes32(0x36299799c00f1e584433782420b22c96b9df65c02cd04f2d48f30d46be856ec5), "h31");
    }
    function testH32() public view {
        require(t.h32() == bytes32(0x2cfe17dc69e953b28d77cdb7cdc86ce378dfe1e846f4be9cbe9dfb18efa5dfb5), "h32");
    }
    function testH33() public view {
        require(t.h33() == bytes32(0xd529e5852759a362ba426afed12b33dfb83d9029bcaa3cdd3e865dc904828fcb), "h33");
    }
    function testShaStored() public view {
        require(t.shaStored() == bytes32(0xb9ea0a42b00fed95e53c20d121a9d3769cb993beccb2eb2184f97ff9e0f818d8), "sha");
    }
    function testHenc() public view {
        require(t.henc() == bytes32(0x69f3a7d692ca055c9f54ae9803e527761c5593a4715f41502d94fbcadbbffbe7), "henc");
    }
    function testHencp() public view {
        require(t.hencp() == bytes32(0xae6299332bcd708cd60e3a8defa55de28078a50a4cf2b3de3a546253240ff9e1), "hencp");
    }
    function testHbox() public view {
        require(t.hbox() == bytes32(0xccad3f5300e77cf5347e3c6200a08bd8cf71f94a0b347bcb39486b17b88a8a71), "hbox");
    }
    function testHmap() public view {
        require(t.hmap() == bytes32(0x6619b407baede597919db7245e6662bd28bed07dad7580f0769d0e94bd0c16fe), "hmap");
    }
    function testHmem() public view {
        require(t.hmem() == bytes32(0x6ccdf593017c9d38b36c1cb00572feae81abc15173860a4e0904a6c45d3b086e), "hmem");
    }
    function testHstr() public view {
        require(t.hstr() == bytes32(0x1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8), "hstr");
    }
    function testHpstored() public view {
        require(t.hpstored() == bytes32(0x6ccdf593017c9d38b36c1cb00572feae81abc15173860a4e0904a6c45d3b086e), "hpstored");
    }
}
