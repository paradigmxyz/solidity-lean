// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {
    OpenZeppelinArraysHarness
} from "../src/OpenZeppelinArrays.sol";

contract OpenZeppelinArraysForgeTest {
    function sortedMemory() internal pure returns (uint256[] memory array) {
        array = new uint256[](4);
        array[0] = 1;
        array[1] = 3;
        array[2] = 3;
        array[3] = 7;
    }

    function testMemoryLowerAndUpperBounds() public {
        OpenZeppelinArraysHarness target = new OpenZeppelinArraysHarness();
        uint256[] memory array = sortedMemory();

        require(target.lowerMemory(array, 0) == 0, "lower before first");
        require(target.lowerMemory(array, 3) == 1, "lower repeated");
        require(target.upperMemory(array, 3) == 3, "upper repeated");
        require(target.lowerMemory(array, 4) == 3, "lower gap");
        require(target.upperMemory(array, 7) == 4, "upper last");
        require(target.upperMemory(array, 9) == 4, "upper after last");
    }

    function testMemoryEmptyBounds() public {
        OpenZeppelinArraysHarness target = new OpenZeppelinArraysHarness();
        uint256[] memory empty = new uint256[](0);

        require(target.lowerMemory(empty, 5) == 0, "empty lower");
        require(target.upperMemory(empty, 5) == 0, "empty upper");
    }

    function testStorageLowerUpperAndFindUpper() public {
        OpenZeppelinArraysHarness target = new OpenZeppelinArraysHarness();

        require(target.lowerStorage(1) == 0, "empty storage lower");
        require(target.seedSorted() == 4, "seed length");
        require(target.length() == 4, "stored length");
        require(target.at(0) == 1, "at 0");
        require(target.at(1) == 3, "at 1");
        require(target.at(2) == 3, "at 2");
        require(target.at(3) == 7, "at 3");

        require(target.lowerStorage(3) == 1, "storage lower repeated");
        require(target.upperStorage(3) == 3, "storage upper repeated");
        require(target.findUpperStorage(3) == 2, "storage find upper repeated");
        require(target.lowerStorage(4) == 3, "storage lower gap");
        require(target.upperStorage(7) == 4, "storage upper last");
    }

    function testAverageAvoidsOverflow() public {
        OpenZeppelinArraysHarness target = new OpenZeppelinArraysHarness();

        require(target.average(2, 8) == 5, "ordinary average");
        require(
            target.average(type(uint256).max, type(uint256).max) ==
                type(uint256).max,
            "max average"
        );
    }
}
