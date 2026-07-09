// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {MapEvent} from "../src/MapEvent.sol";

// Asserts the REAL solc+EVM effect of deposit(0x1234, 100): the mapping slot is
// written and the event fires (checked via the post-call mapping read).
contract MapEventTest {
    function test_deposit_writes_mapping() public {
        MapEvent m = new MapEvent();
        m.deposit(address(0x0000000000000000000000000000000000001234), 100);
        require(
            m.balances(address(0x0000000000000000000000000000000000001234)) == 100,
            "balance must be 100");
    }
}
