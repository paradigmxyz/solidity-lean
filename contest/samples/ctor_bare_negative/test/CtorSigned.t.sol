// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {CtorSigned} from "../src/CtorSigned.sol";

// The claim is rejected as malformed before measurement; kept trivially valid.
contract CtorSignedTest {
    function test_identity() public {
        CtorSigned c = new CtorSigned(-5);
        require(c.f() == -5, "identity");
    }
}
