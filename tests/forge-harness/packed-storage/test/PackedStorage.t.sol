// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {PackedStorageHarnessTarget} from "../src/PackedStorage.sol";

contract PackedStorageForgeTest {
    function testTopLevelPackedValues() public {
        PackedStorageHarnessTarget target = new PackedStorageHarnessTarget();
        require(target.setTopLevel() == 9, "set top");

        (uint8 a, uint16 b, bool c, int8 s, uint256 d) =
            target.readTopLevel();
        require(a == 0x12, "a");
        require(b == 0x3456, "b");
        require(c, "c");
        require(s == -1, "s");
        require(d == 9, "d");
    }

    function testPackedStructAndArrayValues() public {
        PackedStorageHarnessTarget target = new PackedStorageHarnessTarget();
        require(target.setStructAndArray() == 11, "set nested");

        (uint8 a, uint16 b, bool c, int8 s, uint256 d) =
            target.readStruct();
        require(a == 0x12, "a");
        require(b == 0x3456, "b");
        require(c, "c");
        require(s == -1, "s");
        require(d == 9, "d");

        (
            uint8 first,
            uint8 second,
            uint8 third,
            uint8 fourth,
            uint256 tail,
            uint256 afterFixed
        ) = target.readFixeds();
        require(first == 0xaa, "first");
        require(second == 0xbb, "second");
        require(third == 0xcc, "third");
        require(fourth == 0xdd, "fourth");
        require(tail == 10, "tail");
        require(afterFixed == 11, "after fixed");
    }
}
