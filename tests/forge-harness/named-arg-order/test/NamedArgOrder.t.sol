// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {NamedArgOrderHarnessTarget} from "../src/NamedArgOrder.sol";

// Ground truth: solc 0.8.35 LEGACY on real EVM. Named arguments of an internal
// call evaluate in PARAMETER order under legacy codegen (see the contract
// header). These values were captured from a real Forge run and match
// solidity-lean's own-call execution.
contract NamedArgOrderForgeTest {
    NamedArgOrderHarnessTarget private target = new NamedArgOrderHarnessTarget();

    // positional: source order => 12 (shared by legacy and via-IR).
    function testPositionalOrder() public {
        require(target.positionalOrder() == 12, "positional order must be 12");
    }

    // internal named, 2 args: LEGACY parameter order => 21.
    function testInternalOrder() public {
        require(target.internalOrder() == 21, "internal named-arg order must be 21");
    }

    // internal named, 3 args scrambled {c,a,b}: LEGACY parameter order => 231.
    function testInternalThree() public {
        require(target.internalThree() == 231, "internal 3-arg named order must be 231");
    }
}
