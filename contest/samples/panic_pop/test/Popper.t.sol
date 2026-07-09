// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Popper} from "../src/Popper.sol";

// Asserts the REAL solc+EVM behavior: f() with an empty array reverts with
// Panic(0x31) (pop on empty array), byte-for-byte.
contract PopperTest {
    function test_pop_empty_panics() public {
        Popper p = new Popper();
        try p.f() returns (uint256) {
            require(false, "expected pop-empty panic");
        } catch (bytes memory data) {
            require(
                keccak256(data) ==
                    keccak256(abi.encodeWithSignature("Panic(uint256)", uint256(0x31))),
                "must revert with Panic(0x31)");
        }
    }
}
