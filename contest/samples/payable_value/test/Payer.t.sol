// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Payer} from "../src/Payer.sol";

// Asserts the REAL solc+EVM behavior: f{value: 1000}() returns 1000 (msg.value).
contract PayerTest {
    function test_returns_msg_value() public {
        Payer p = new Payer();
        uint256 got = p.f{value: 1000}();
        require(got == 1000, "must return msg.value 1000");
    }
}
