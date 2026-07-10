// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {TernaryStoragePointerHarnessTarget} from "../src/TernaryStoragePointer.sol";

// Real-EVM ground truth for G#116: a ternary storage pointer aliases the
// SELECTED state variable. Each test deploys a fresh target so state does not
// leak between cases.
contract TernaryStoragePointerForgeTest {
    // b = true selects s0: writing through p mutates s0, leaves s1 at 0.
    function testAliasTrueSelectsS0() public {
        TernaryStoragePointerHarnessTarget target =
            new TernaryStoragePointerHarnessTarget();
        require(target.aliasSelected(true, 42) == 42, "selected s0 == 42");
        require(target.getS0() == 42, "s0 slot written");
        require(target.getS1() == 0, "s1 slot untouched");
    }

    // b = false selects s1: writing through p mutates s1, leaves s0 at 0.
    function testAliasFalseSelectsS1() public {
        TernaryStoragePointerHarnessTarget target =
            new TernaryStoragePointerHarnessTarget();
        require(target.aliasSelected(false, 99) == 99, "selected s1 == 99");
        require(target.getS1() == 99, "s1 slot written");
        require(target.getS0() == 0, "s0 slot untouched");
    }

    // The write must NOT leak into the unselected slot (either direction).
    function testOtherUntouched() public {
        TernaryStoragePointerHarnessTarget target =
            new TernaryStoragePointerHarnessTarget();
        require(target.otherUntouched(true, 42) == 0, "s1 untouched when b=true");
        TernaryStoragePointerHarnessTarget target2 =
            new TernaryStoragePointerHarnessTarget();
        require(target2.otherUntouched(false, 42) == 0, "s0 untouched when b=false");
    }

    // Read-through of the ternary pointer sees the selected slot's value.
    function testReadThrough() public {
        TernaryStoragePointerHarnessTarget target =
            new TernaryStoragePointerHarnessTarget();
        target.aliasSelected(true, 7); // s0.x = 7
        require(target.readThrough(true) == 7, "read s0 through pointer");
        require(target.readThrough(false) == 0, "read s1 through pointer");
    }

    // Ternary storage reference passed to a `storage`-ref parameter reads the
    // selected slot.
    function testPassToStorageParam() public {
        TernaryStoragePointerHarnessTarget target =
            new TernaryStoragePointerHarnessTarget();
        target.aliasSelected(false, 21); // s1.x = 21
        require(target.passToStorageParam(true) == 0, "param reads s0");
        require(target.passToStorageParam(false) == 21, "param reads s1");
    }
}
