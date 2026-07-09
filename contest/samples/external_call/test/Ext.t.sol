// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Ext} from "../src/Ext.sol";

contract ExtTest {
    function test_probe() public {
        Ext e = new Ext();
        // low-level call to a codeless address succeeds (true) on real EVM.
        require(e.probe(address(0x1234)) == true, "expected true");
    }
}
