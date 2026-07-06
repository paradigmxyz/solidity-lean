// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinDoubleEndedQueue,
    OpenZeppelinDoubleEndedQueueHarness
} from "../src/OpenZeppelinDoubleEndedQueue.sol";

contract OpenZeppelinDoubleEndedQueueForgeTest {
    function word(uint256 value) internal pure returns (bytes32) {
        return bytes32(value);
    }

    function testPushPopBothEndsAndSignedWindow() public {
        OpenZeppelinDoubleEndedQueueHarness target =
            new OpenZeppelinDoubleEndedQueueHarness();

        require(target.empty(), "initial empty");
        require(target.length() == 0, "initial length");
        require(target.pushBack(word(0x11)) == 1, "push back");
        require(target.front() == word(0x11), "front one");
        require(target.back() == word(0x11), "back one");

        require(target.pushFront(word(0x22)) == 2, "push front");
        require(target.front() == word(0x22), "front two");
        require(target.back() == word(0x11), "back two");
        require(target.at(0) == word(0x22), "at zero");
        require(target.at(1) == word(0x11), "at one");

        require(target.pushBack(word(0x33)) == 3, "push back again");
        require(target.at(2) == word(0x33), "at two");
        require(target.popFront() == word(0x22), "pop front");
        require(target.popBack() == word(0x33), "pop back");
        require(target.popBack() == word(0x11), "pop final");
        require(target.empty(), "empty after pops");
    }

    function testClearResetsWindowAndAllowsReuse() public {
        OpenZeppelinDoubleEndedQueueHarness target =
            new OpenZeppelinDoubleEndedQueueHarness();

        target.pushBack(word(0xaa));
        target.pushFront(word(0xbb));
        require(target.clear() == 0, "clear length");
        require(target.empty(), "empty after clear");

        target.pushBack(word(0xcc));
        require(target.front() == word(0xcc), "front after reuse");
        require(target.length() == 1, "length after reuse");
    }

    function testEmptyAndBoundsRevert() public {
        OpenZeppelinDoubleEndedQueueHarness target =
            new OpenZeppelinDoubleEndedQueueHarness();

        try target.popFront() returns (bytes32) {
            revert("expected empty pop");
        } catch (bytes memory reason) {
            require(
                keccak256(reason) ==
                    keccak256(
                        abi.encodeWithSelector(
                            OpenZeppelinDoubleEndedQueue.Empty.selector
                        )
                    ),
                "empty reason"
            );
        }

        target.pushBack(word(0x44));
        try target.at(1) returns (bytes32) {
            revert("expected out of bounds");
        } catch (bytes memory reason) {
            require(
                keccak256(reason) ==
                    keccak256(
                        abi.encodeWithSelector(
                            OpenZeppelinDoubleEndedQueue.OutOfBounds.selector
                        )
                    ),
                "bounds reason"
            );
        }
    }

    function testSafeCastRevertForHugeIndex() public {
        OpenZeppelinDoubleEndedQueueHarness target =
            new OpenZeppelinDoubleEndedQueueHarness();
        target.pushBack(word(0x55));

        uint256 tooLarge = uint256(type(int256).max) + 1;
        try target.at(tooLarge) returns (bytes32) {
            revert("expected int256 cast failure");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("SafeCast: value doesn't fit in an int256")),
                "safe cast reason"
            );
        }
    }
}
