// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Indexer} from "../src/Indexer.sol";

// Asserts the REAL solc+EVM behavior: f(5) on a length-2 array reverts with
// Panic(0x32) (array out-of-bounds), byte-for-byte.
contract IndexerTest {
    function test_oob_panics() public {
        Indexer p = new Indexer();
        try p.f(5) returns (uint256) {
            require(false, "expected out-of-bounds panic");
        } catch (bytes memory data) {
            require(
                keccak256(data) ==
                    keccak256(abi.encodeWithSignature("Panic(uint256)", uint256(0x32))),
                "must revert with Panic(0x32)");
        }
    }
}
