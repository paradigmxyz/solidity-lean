// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {UsingForWidenHarnessTarget} from "../src/UsingForWiden.sol";

contract UsingForWidenForgeTest {
    UsingForWidenHarnessTarget private target =
        new UsingForWidenHarnessTarget();

    // uint8 receiver 255 widened (zero-extended) to uint256 first param of `f`:
    // 255 + 1 = 256, NO truncation to uint8.
    function testWidenReceiverMax() public view {
        require(target.widenReceiver(255) == 256, "widen receiver 255 -> 256");
    }

    function testWidenReceiverSmall() public view {
        require(target.widenReceiver(5) == 6, "widen receiver 5 -> 6");
    }

    // uint256 receiver (exact self) + uint8 additional arg 255 widened to uint256.
    function testWidenAddArg() public view {
        require(
            target.widenAddArg(1000, 255) == 1255,
            "widen add-arg 1000 + 255 -> 1255"
        );
    }
}
