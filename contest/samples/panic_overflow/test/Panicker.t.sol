// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Panicker} from "../src/Panicker.sol";

// Asserts the REAL solc+EVM behavior: f(type(uint256).max) reverts with
// Panic(0x11) (arithmetic overflow), byte-for-byte.
contract PanickerTest {
    function test_overflow_panics() public {
        Panicker p = new Panicker();
        try p.f(type(uint256).max) returns (uint256) {
            require(false, "expected overflow panic");
        } catch (bytes memory data) {
            require(
                keccak256(data) ==
                    keccak256(abi.encodeWithSignature("Panic(uint256)", uint256(0x11))),
                "must revert with Panic(0x11)");
        }
    }
}
