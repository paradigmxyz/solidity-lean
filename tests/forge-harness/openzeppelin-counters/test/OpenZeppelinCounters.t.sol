// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {OpenZeppelinCountersHarness} from "../src/OpenZeppelinCounters.sol";

contract OpenZeppelinCountersForgeTest {
    function _expectString(bytes memory actual, string memory expected)
        private
        pure
    {
        require(
            keccak256(actual) == keccak256(abi.encodeWithSignature(
                "Error(string)",
                expected
            )),
            "revert string"
        );
    }

    function testIncrementDecrementAndReset() public {
        OpenZeppelinCountersHarness target =
            new OpenZeppelinCountersHarness();

        require(target.current() == 0, "initial");
        require(target.increment() == 1, "increment");
        require(target.increment() == 2, "increment again");
        require(target.decrement() == 1, "decrement");

        target.reset();
        require(target.current() == 0, "reset");
        require(target.incrementByTwo() == 2, "increment by two");
    }

    function testIndependentCounters() public {
        OpenZeppelinCountersHarness target =
            new OpenZeppelinCountersHarness();

        require(target.increment() == 1, "ids increment");
        require(target.incrementOther() == 1, "other increment");
        require(target.incrementOther() == 2, "other increment again");
        require(target.current() == 1, "ids unchanged");
        require(target.other() == 2, "other stored");
        require(target.decrementOther() == 1, "other decrement");
        require(target.current() == 1, "ids still unchanged");
    }

    function testDecrementRevertsAndRollsBack() public {
        OpenZeppelinCountersHarness target =
            new OpenZeppelinCountersHarness();

        try target.decrement() returns (uint256) {
            revert("expected decrement failure");
        } catch (bytes memory reason) {
            _expectString(reason, "Counter: decrement overflow");
        }
        require(target.current() == 0, "ids rollback");

        require(target.incrementOther() == 1, "other increment");
        require(target.decrementOther() == 0, "other decrement to zero");
        try target.decrementOther() returns (uint256) {
            revert("expected other failure");
        } catch (bytes memory reason) {
            _expectString(reason, "Counter: decrement overflow");
        }
        require(target.other() == 0, "other rollback");
    }
}
