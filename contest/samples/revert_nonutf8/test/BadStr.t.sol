// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {BadStr} from "../src/BadStr.sol";

// Asserts the REAL solc+EVM behavior: f() reverts with an Error(string) whose
// payload bytes are 0xff 0xfe 'o' 'k'.
contract BadStrTest {
    function test_nonutf8_reason() public {
        BadStr p = new BadStr();
        try p.f() returns (uint256) {
            require(false, "expected revert");
        } catch (bytes memory data) {
            bytes memory expected = abi.encodeWithSignature(
                "Error(string)", string(abi.encodePacked(bytes1(0xff), bytes1(0xfe), "ok")));
            require(keccak256(data) == keccak256(expected), "non-utf8 reason mismatch");
        }
    }
}
