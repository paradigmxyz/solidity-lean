// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {RecursiveStructMemConstructHarness} from "../src/RecursiveStructMemConstruct.sol";

contract RecursiveStructMemConstructForgeTest {
    RecursiveStructMemConstructHarness private harness =
        new RecursiveStructMemConstructHarness();

    // G3: the self-referential memory construction returns its `v` field.
    function testConstructRecursive() public view {
        require(harness.constructRecursive() == 1, "recursive struct mem construct");
    }

    // H1: dyn-array member of a value type.
    function testConstructFlat() public view {
        require(harness.constructFlat() == 2, "flat struct mem construct");
    }

    // H2: dyn-array member of a different struct.
    function testConstructBox() public view {
        require(harness.constructBox() == 3, "box struct mem construct");
    }

    // G1: storage field write on the recursive struct.
    function testStorageWrite() public {
        require(harness.storageWrite() == 5, "recursive struct storage write");
    }
}
