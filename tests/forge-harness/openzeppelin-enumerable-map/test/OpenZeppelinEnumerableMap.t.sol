// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinEnumerableMapHarness
} from "../src/OpenZeppelinEnumerableMap.sol";

contract OpenZeppelinEnumerableMapForgeTest {
    function testUintToAddressSetUpdateTryGetAndEvents() public {
        OpenZeppelinEnumerableMapHarness target =
            new OpenZeppelinEnumerableMapHarness();

        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        require(target.ownerLength() == 0, "initial length");
        require(!target.ownerContains(7), "initial contains");

        require(target.setOwner(7, alice), "fresh set");
        require(target.ownerContains(7), "contains");
        require(target.ownerLength() == 1, "length 1");
        require(target.ownerGet(7) == alice, "get alice");

        (bool found, address owner) = target.ownerTryGet(7);
        require(found, "try found");
        require(owner == alice, "try alice");

        require(!target.setOwner(7, bob), "update not fresh");
        require(target.ownerLength() == 1, "update length");
        require(target.ownerGet(7) == bob, "get bob");

        (uint256 key, address indexedOwner) = target.ownerAt(0);
        require(key == 7, "at key");
        require(indexedOwner == bob, "at value");
    }

    function testRemoveMiddleSwapsAndDeletesOwner() public {
        OpenZeppelinEnumerableMapHarness target =
            new OpenZeppelinEnumerableMapHarness();

        address alice = address(0xA11CE);
        address bob = address(0xB0B);
        address carol = address(0xCA801);

        require(target.seedThree(alice, bob, carol) == 3, "seed");
        require(target.removeOwner(22), "remove middle");
        require(target.ownerLength() == 2, "length 2");
        require(!target.ownerContains(22), "removed contains");

        (bool found, address removed) = target.ownerTryGet(22);
        require(!found, "missing found");
        require(removed == address(0), "missing default");

        (uint256 key0, address owner0) = target.ownerAt(0);
        (uint256 key1, address owner1) = target.ownerAt(1);
        require(key0 == 11, "key0");
        require(owner0 == alice, "owner0");
        require(key1 == 33, "key1");
        require(owner1 == carol, "owner1");
        require(!target.removeOwner(99), "remove missing");
    }

    function testAddressToUintZeroValueAndMissingGetRevert() public {
        OpenZeppelinEnumerableMapHarness target =
            new OpenZeppelinEnumerableMapHarness();

        address alice = address(0xA11CE);
        address bob = address(0xB0B);

        require(target.setBalance(alice, 0), "fresh zero");
        require(target.balanceContains(alice), "contains zero");
        require(target.balanceLength() == 1, "length zero");

        (bool foundZero, uint256 zeroValue) = target.balanceTryGet(alice);
        require(foundZero, "try zero found");
        require(zeroValue == 0, "try zero value");
        require(target.balanceGet(alice) == 0, "get zero");

        require(target.setBalance(bob, 99), "fresh bob");
        (address account0, uint256 balance0) = target.balanceAt(0);
        (address account1, uint256 balance1) = target.balanceAt(1);
        require(account0 == alice, "account0");
        require(balance0 == 0, "balance0");
        require(account1 == bob, "account1");
        require(balance1 == 99, "balance1");

        require(target.removeBalance(alice), "remove alice");
        require(!target.balanceContains(alice), "alice removed");

        try target.balanceGet(alice) {
            revert("expected missing balance");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("EnumerableMap: nonexistent key")),
                "missing reason"
            );
        }
    }
}
