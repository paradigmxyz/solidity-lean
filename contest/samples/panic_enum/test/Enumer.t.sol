// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Enumer} from "../src/Enumer.sol";

// Asserts the REAL solc+EVM behavior: f(5) on a 3-member enum reverts with
// Panic(0x21) (invalid enum conversion), byte-for-byte.
contract EnumerTest {
    function test_enum_oob_panics() public {
        Enumer p = new Enumer();
        try p.f(5) returns (uint256) {
            require(false, "expected enum conversion panic");
        } catch (bytes memory data) {
            require(
                keccak256(data) ==
                    keccak256(abi.encodeWithSignature("Panic(uint256)", uint256(0x21))),
                "must revert with Panic(0x21)");
        }
    }
}
