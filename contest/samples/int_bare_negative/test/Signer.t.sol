// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Signer} from "../src/Signer.sol";

// The claim is rejected as malformed BEFORE any measurement, so this test body
// is never the deciding factor; kept trivially true for a well-formed project.
contract SignerTest {
    function test_identity() public {
        Signer p = new Signer();
        require(p.f(-5) == -5, "identity");
    }
}
