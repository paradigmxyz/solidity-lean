// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {OpenZeppelinTimeHarness} from "../src/OpenZeppelinTime.sol";

interface Vm {
    function warp(uint256 timestamp) external;
    function roll(uint256 blockNumber) external;
}

contract OpenZeppelinTimeForgeTest {
    Vm private constant vm =
        Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function _expectCustom(bytes memory actual, bytes memory expected)
        private
        pure
    {
        require(keccak256(actual) == keccak256(expected), "custom error");
    }

    function testClockAccessorsAndPacking() public {
        OpenZeppelinTimeHarness target = new OpenZeppelinTimeHarness();

        vm.warp(123);
        vm.roll(456);
        require(target.timestampNow() == 123, "timestamp");
        require(target.blockNumberNow() == 456, "block number");

        (
            uint32 valueBefore,
            uint32 valueAfter,
            uint48 effect
        ) = target.packUnpack(3, 7, 99);

        require(valueBefore == 3, "before");
        require(valueAfter == 7, "after");
        require(effect == 99, "effect");
    }

    function testStoredDelayAndIncreaseSchedule() public {
        OpenZeppelinTimeHarness target = new OpenZeppelinTimeHarness();

        vm.warp(100);
        require(target.store(5) == 5, "store");
        require(target.current() == 5, "current");

        (uint32 beforeValue, uint32 afterValue, uint48 effect) =
            target.full();
        require(beforeValue == 5, "full before");
        require(afterValue == 0, "full after");
        require(effect == 0, "full effect");

        uint32 currentValue;
        (beforeValue, afterValue, effect, currentValue) = target.schedule(9, 3);
        require(beforeValue == 5, "scheduled before");
        require(afterValue == 9, "scheduled after");
        require(effect == 103, "scheduled effect");
        require(currentValue == 5, "scheduled current");

        vm.warp(102);
        require(target.current() == 5, "before effect");
        vm.warp(103);
        require(target.current() == 9, "after effect");

        (beforeValue, afterValue, effect) = target.full();
        require(beforeValue == 9, "settled before");
        require(afterValue == 0, "settled after");
        require(effect == 0, "settled effect");
    }

    function testDecreaseScheduleUsesOldDelayDifference() public {
        OpenZeppelinTimeHarness target = new OpenZeppelinTimeHarness();

        vm.warp(200);
        require(target.store(10) == 10, "store");

        (
            uint32 beforeValue,
            uint32 afterValue,
            uint48 effect,
            uint32 currentValue
        ) = target.schedule(4, 3);

        require(beforeValue == 10, "decrease before");
        require(afterValue == 4, "decrease after");
        require(effect == 206, "decrease effect");
        require(currentValue == 10, "decrease current");

        vm.warp(205);
        require(target.current() == 10, "old delay still active");
        vm.warp(206);
        require(target.current() == 4, "new delay active");
    }

    function testSafeCastOverflowReverts() public {
        OpenZeppelinTimeHarness target = new OpenZeppelinTimeHarness();

        uint256 tooLarge = uint256(type(uint48).max) + 1;
        vm.warp(tooLarge);

        try target.timestampNow() returns (uint48) {
            revert("expected revert");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSignature(
                    "SafeCastOverflowedUintDowncast(uint8,uint256)",
                    48,
                    tooLarge
                )
            );
        }
    }
}
