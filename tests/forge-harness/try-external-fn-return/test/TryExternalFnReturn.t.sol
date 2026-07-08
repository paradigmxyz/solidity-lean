// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {
    IProvider,
    Provider,
    TryExternalFnReturnHarnessTarget
} from "../src/TryExternalFnReturn.sol";

// Forge ground truth for G18: the external function pointer bound by
// `try ... returns (function() external ...)` round-trips and, when invoked,
// yields the callee's value (42).
contract TryExternalFnReturnForgeTest {
    function testTryGetAndCall() public {
        TryExternalFnReturnHarnessTarget caller =
            new TryExternalFnReturnHarnessTarget();
        Provider p = new Provider();
        require(caller.tryGetAndCall(IProvider(address(p))) == 42, "round-trip");
    }
}
