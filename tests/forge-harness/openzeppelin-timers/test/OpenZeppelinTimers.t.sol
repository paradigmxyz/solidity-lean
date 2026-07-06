// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {OpenZeppelinTimersHarness} from "../src/OpenZeppelinTimers.sol";

interface Vm {
    function warp(uint256 timestamp) external;
    function roll(uint256 blockNumber) external;
}

contract OpenZeppelinTimersForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function testTimestampLifecycle() public {
        OpenZeppelinTimersHarness target = new OpenZeppelinTimersHarness();

        vm.warp(100);
        require(target.timestampDeadline() == 0, "initial timestamp deadline");
        require(target.timestampIsUnset(), "initial timestamp unset");
        require(!target.timestampIsStarted(), "initial timestamp started");
        require(!target.timestampIsPending(), "initial timestamp pending");
        require(!target.timestampIsExpired(), "initial timestamp expired");

        require(target.setTimestampDeadline(120), "timestamp pending");
        require(target.timestampIsStarted(), "timestamp started");
        require(!target.timestampIsExpired(), "timestamp not expired");

        vm.warp(120);
        require(target.timestampDeadline() == 120, "timestamp deadline");
        require(!target.timestampIsUnset(), "timestamp set");
        require(target.timestampIsStarted(), "timestamp still started");
        require(!target.timestampIsPending(), "timestamp no longer pending");
        require(target.timestampIsExpired(), "timestamp expired now");

        require(target.resetTimestampDeadline(), "timestamp reset");
        require(target.timestampDeadline() == 0, "timestamp reset deadline");
        require(target.timestampIsUnset(), "timestamp reset unset");
        require(!target.timestampIsStarted(), "timestamp reset started");
        require(!target.timestampIsPending(), "timestamp reset pending");
        require(!target.timestampIsExpired(), "timestamp reset expired");
    }

    function testBlockNumberLifecycle() public {
        OpenZeppelinTimersHarness target = new OpenZeppelinTimersHarness();

        vm.roll(40);
        require(target.blockNumberDeadline() == 0, "initial block deadline");
        require(target.blockNumberIsUnset(), "initial block unset");
        require(!target.blockNumberIsStarted(), "initial block started");
        require(!target.blockNumberIsPending(), "initial block pending");
        require(!target.blockNumberIsExpired(), "initial block expired");

        require(target.setBlockNumberDeadline(42), "block pending");
        require(target.blockNumberIsStarted(), "block started");
        require(!target.blockNumberIsExpired(), "block not expired");

        vm.roll(42);
        require(target.blockNumberDeadline() == 42, "block deadline");
        require(!target.blockNumberIsUnset(), "block set");
        require(target.blockNumberIsStarted(), "block still started");
        require(!target.blockNumberIsPending(), "block no longer pending");
        require(target.blockNumberIsExpired(), "block expired now");

        require(target.resetBlockNumberDeadline(), "block reset");
        require(target.blockNumberDeadline() == 0, "block reset deadline");
        require(target.blockNumberIsUnset(), "block reset unset");
        require(!target.blockNumberIsStarted(), "block reset started");
        require(!target.blockNumberIsPending(), "block reset pending");
        require(!target.blockNumberIsExpired(), "block reset expired");
    }
}
