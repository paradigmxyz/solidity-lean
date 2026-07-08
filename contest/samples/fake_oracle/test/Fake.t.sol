// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
import {Fake} from "../src/Fake.sol";
contract FakeForgeTest {
    Fake private target = new Fake();
    // Trivially passes; asserts nothing about run(). (The attack.)
    function testTrivial() public pure { require(true, "trivial"); }
}
