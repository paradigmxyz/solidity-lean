// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/LocalPointerDefinite.sol";

contract LocalPointerDefiniteForgeTest {
    LocalPointerDefinite private target;

    function setUp() public {
        target = new LocalPointerDefinite();
    }

    function testStorageDelayedAndBranchAssignment() public view {
        require(target.storageStraight() == 0);
        require(target.storageBranch(true) == 0);
        require(target.storageBranch(false) == 0);
        require(target.storageDoWhile() == 0);
    }

    function testStorageMutationAfterAssignment() public {
        require(target.pushThrough(17) == 17);
        require(target.storageStraight() == 1);
    }

    function testCalldataDelayedAndBranchAssignment() public view {
        bytes memory first = hex"010203";
        bytes memory second = hex"aabb";
        require(target.calldataStraight(first) == 3);
        require(target.calldataBranch(first, second, true) == 3);
        require(target.calldataBranch(first, second, false) == 2);
    }

    function testUnusedAndShadowedPointers() public view {
        target.unusedPointers();
        require(target.shadowed(hex"01020304") == 4);
    }
}
