// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {
    OpenZeppelinCheckpointsHarness,
    OpenZeppelinCheckpoints
} from "../src/OpenZeppelinCheckpoints.sol";

contract OpenZeppelinCheckpointsForgeTest {
    function testPushLatestAtAndUpdate() public {
        OpenZeppelinCheckpointsHarness target =
            new OpenZeppelinCheckpointsHarness();

        require(target.length() == 0, "initial length");
        require(target.latest() == 0, "initial latest");

        (bool exists0, uint256 key0, uint256 value0) =
            target.latestCheckpoint();
        require(!exists0 && key0 == 0 && value0 == 0, "empty checkpoint");

        (uint256 oldValue, uint256 newValue) = target.push(5, 10);
        require(oldValue == 0 && newValue == 10, "first push tuple");
        require(target.length() == 1, "first length");
        require(target.latest() == 10, "first latest");
        require(target.keyAt(0) == 5, "first key");
        require(target.valueAt(0) == 10, "first value");

        (bool exists1, uint256 key1, uint256 value1) =
            target.latestCheckpoint();
        require(exists1 && key1 == 5 && value1 == 10, "latest checkpoint");

        (oldValue, newValue) = target.push(5, 12);
        require(oldValue == 10 && newValue == 12, "update tuple");
        require(target.length() == 1, "update length");
        require(target.latest() == 12, "update latest");
        require(target.valueAt(0) == 12, "updated stored value");
    }

    function testLowerAndUpperLookups() public {
        OpenZeppelinCheckpointsHarness target =
            new OpenZeppelinCheckpointsHarness();

        require(target.pushThree(10, 100, 20, 200, 30, 300) == 3, "seed");

        require(target.lowerLookup(5) == 100, "lower before first");
        require(target.lowerLookup(10) == 100, "lower exact first");
        require(target.lowerLookup(15) == 200, "lower gap");
        require(target.lowerLookup(25) == 300, "lower gap high");
        require(target.lowerLookup(40) == 0, "lower after last");

        require(target.upperLookup(5) == 0, "upper before first");
        require(target.upperLookup(10) == 100, "upper exact first");
        require(target.upperLookup(15) == 100, "upper gap");
        require(target.upperLookup(30) == 300, "upper exact last");
        require(target.upperLookup(40) == 300, "upper after last");
        require(target.upperLookupRecent(25) == 200, "upper recent");
    }

    function testUnorderedInsertionRevertsAndRollsBack() public {
        OpenZeppelinCheckpointsHarness target =
            new OpenZeppelinCheckpointsHarness();

        target.push(2, 20);

        try target.push(1, 10) {
            revert("expected unordered revert");
        } catch (bytes memory reason) {
            require(
                bytes4(reason) ==
                    OpenZeppelinCheckpoints
                        .CheckpointUnorderedInsertion
                        .selector,
                "unordered selector"
            );
        }

        require(target.length() == 1, "length rolled back");
        require(target.latest() == 20, "latest rolled back");
        require(target.keyAt(0) == 2, "key rolled back");
        require(target.valueAt(0) == 20, "value rolled back");
    }
}
