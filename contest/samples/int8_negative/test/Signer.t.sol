// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Signer} from "../src/Signer.sol";

// Asserts the REAL solc+EVM behavior: f(-5) returns int8(-5).
contract SignerTest {
    function test_returns_negative() public {
        Signer p = new Signer();
        int8 got = p.f(-5);
        require(got == -5, "must return -5");
    }
}
