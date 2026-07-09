// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import { CtorArgD } from "../src/ConstructorBaseArgOrder.sol";

contract ConstructorBaseArgOrderForgeTest {
    // Base-constructor arguments are evaluated derived->base during descent,
    // each in the supplying (derived) contract's frame; bodies run base->derived.
    // Order r(4), r(2), r(1), r(3), r(5) -> trace 42135.
    function testBaseArgOrderTrace() public {
        CtorArgD t = new CtorArgD();
        require(t.trace() == 42135, "base-ctor arg order trace");
    }
}
