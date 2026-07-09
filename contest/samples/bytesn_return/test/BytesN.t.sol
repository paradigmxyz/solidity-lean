// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {BytesN} from "../src/BytesN.sol";

contract BytesNForgeTest {
    BytesN private target = new BytesN();

    // Asserts the REAL solc+EVM observable: f() == 0x01020304.
    function testF() public view {
        require(target.f() == bytes4(0x01020304), "f() should be 0x01020304");
    }
}
