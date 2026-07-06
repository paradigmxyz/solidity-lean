// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinEnumerableSetHarness
} from "../src/OpenZeppelinEnumerableSet.sol";

contract OpenZeppelinEnumerableSetForgeTest {
    function testAddDuplicateContainsAndIndex() public {
        OpenZeppelinEnumerableSetHarness target =
            new OpenZeppelinEnumerableSetHarness();

        require(target.length() == 0, "initial length");
        require(!target.contains(11), "initial contains");
        require(target.add(11), "add 11");
        require(target.contains(11), "contains 11");
        require(target.length() == 1, "length 1");
        require(target.at(0) == 11, "at 0");
        require(target.rawIndex(11) == 1, "raw index 11");
        require(!target.add(11), "duplicate 11");
        require(target.length() == 1, "duplicate length");
    }

    function testRemoveMiddleSwapsLastAndDeletesIndex() public {
        OpenZeppelinEnumerableSetHarness target =
            new OpenZeppelinEnumerableSetHarness();

        require(target.addThree(11, 22, 33) == 3, "add three");
        require(target.rawIndex(11) == 1, "raw 11");
        require(target.rawIndex(22) == 2, "raw 22");
        require(target.rawIndex(33) == 3, "raw 33");

        require(target.remove(22), "remove 22");
        require(target.length() == 2, "length 2");
        require(!target.contains(22), "contains removed");
        require(target.rawIndex(22) == 0, "raw removed");
        require(target.at(0) == 11, "kept first");
        require(target.at(1) == 33, "moved last");
        require(target.rawIndex(33) == 2, "raw moved");
    }

    function testRemoveLastAndMissingValue() public {
        OpenZeppelinEnumerableSetHarness target =
            new OpenZeppelinEnumerableSetHarness();

        require(target.addThree(4, 5, 6) == 3, "add three");
        require(target.remove(6), "remove last");
        require(target.length() == 2, "length 2");
        require(target.at(0) == 4, "at 0");
        require(target.at(1) == 5, "at 1");
        require(target.rawIndex(6) == 0, "raw removed");
        require(!target.remove(99), "remove missing");
        require(target.length() == 2, "missing length");
    }
}
