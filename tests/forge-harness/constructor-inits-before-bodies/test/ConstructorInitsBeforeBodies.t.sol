// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import { CtorInitD } from "../src/ConstructorInitsBeforeBodies.sol";

contract ConstructorInitsBeforeBodiesForgeTest {
    // Under LEGACY codegen every inline state-variable initializer (whole
    // hierarchy) runs before any constructor body, so CtorInitD's
    // `observed = trace` reads trace == 0 (the base body has not run yet).
    function testInitsBeforeBodies() public {
        CtorInitD t = new CtorInitD();
        require(t.trace() == 7, "base body ran");
        require(t.observed() == 0, "inits before bodies");
    }
}
