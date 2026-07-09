// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Divver} from "../src/Divver.sol";

// Asserts the REAL solc+EVM behavior: f(1, 0) reverts with Panic(0x12)
// (division/modulo by zero), byte-for-byte.
contract DivverTest {
    function test_divzero_panics() public {
        Divver p = new Divver();
        try p.f(1, 0) returns (uint256) {
            require(false, "expected div-by-zero panic");
        } catch (bytes memory data) {
            require(
                keccak256(data) ==
                    keccak256(abi.encodeWithSignature("Panic(uint256)", uint256(0x12))),
                "must revert with Panic(0x12)");
        }
    }
}
