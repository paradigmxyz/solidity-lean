// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {ArityOverloadBinding} from "../src/ArityOverloadBinding.sol";

/// Ground truth (solc 0.8.35 / Foundry EVM): overload binding for same-arity
/// library overloads where the wrong candidate is declared first — solc binds
/// by type, never by declaration order.
contract ArityOverloadBindingForgeTest {
    ArityOverloadBinding private harness = new ArityOverloadBinding();

    function testAttachedBox() public view {
        require(harness.attachedBox(39) == 42, "x + Box(3).v");
    }

    function testAttachedUint() public view {
        require(harness.attachedUint(10) == 40, "x * 4");
    }

    function testLibDriver() public view {
        require(harness.libDriver(30) == 42, "seed + 5 + 7");
    }

    function testLibDriverUint() public view {
        require(harness.libDriverUint(3) == 3007, "seed * 1000 + 7");
    }
}
