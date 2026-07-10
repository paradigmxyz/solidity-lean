// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ConstGetterPureOverrideHarnessTarget, I} from "../src/ConstGetterPureOverride.sol";

contract ConstGetterPureOverrideForgeTest {
    function testConstGetterReturnsFive() public {
        ConstGetterPureOverrideHarnessTarget t =
            new ConstGetterPureOverrideHarnessTarget();
        require(t.X() == 5, "X()==5 direct");
        // Also reachable through the pure interface the constant getter overrides.
        I i = I(address(t));
        require(i.X() == 5, "X()==5 via interface");
    }
}
