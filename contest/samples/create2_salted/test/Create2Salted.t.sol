// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Create2Salted} from "../src/Create2Salted.sol";

// Plain require-based test (no forge-std): the REAL solc+EVM behavior — the
// salted CREATE2 succeeds and returns the (nonzero) created address. Passes on
// real EVM; the submission is still OUT OF SCOPE (X-EXTCALL contract creation).
contract Create2SaltedTest {
    function test_make_creates() public {
        Create2Salted c = new Create2Salted();
        address a = c.make(1);
        require(a != address(0), "create2 must succeed");
    }
}
