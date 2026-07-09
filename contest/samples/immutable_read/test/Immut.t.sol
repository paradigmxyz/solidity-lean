// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {Immut} from "../src/Immut.sol";

// Asserts the REAL solc+EVM behavior: f() returns the constructor-set immutable 42.
contract ImmutTest {
    function test_returns_immutable() public {
        Immut p = new Immut();
        require(p.f() == 42, "must return immutable 42");
    }
}
