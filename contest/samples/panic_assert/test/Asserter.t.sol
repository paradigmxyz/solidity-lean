// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Asserter} from "../src/Asserter.sol";

// Asserts the REAL solc+EVM behavior: f(0) reverts with Panic(0x01)
// (assertion failure), byte-for-byte.
contract AsserterTest {
    function test_assert_panics() public {
        Asserter p = new Asserter();
        try p.f(0) returns (uint256) {
            require(false, "expected assert panic");
        } catch (bytes memory data) {
            require(
                keccak256(data) ==
                    keccak256(abi.encodeWithSignature("Panic(uint256)", uint256(0x01))),
                "must revert with Panic(0x01)");
        }
    }
}
