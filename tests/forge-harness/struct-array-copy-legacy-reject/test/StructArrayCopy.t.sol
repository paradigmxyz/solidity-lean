// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {StructArrayCopyHarnessTarget} from "../src/StructArrayCopy.sol";

// Pins the runtime values of the ACCEPTED-control copies on the EVM. These are
// the shapes solc 0.8.35 legacy codegen accepts (element is not a struct, or the
// value is a struct rather than an array-of-struct); the fix keeps them accepted.
contract StructArrayCopyForgeTest {
    StructArrayCopyHarnessTarget private target =
        new StructArrayCopyHarnessTarget();

    function testStringArrayMemoryToStorage() public {
        string[] memory m = new string[](2);
        m[0] = "hello";
        m[1] = "world";
        target.setWords(m);
        require(target.wordCount() == 2, "wordCount");
        require(
            keccak256(bytes(target.wordAt(0))) == keccak256(bytes("hello")),
            "wordAt0"
        );
        require(
            keccak256(bytes(target.wordAt(1))) == keccak256(bytes("world")),
            "wordAt1"
        );
    }

    function testUintNestedArrayMemoryToStorage() public {
        uint256[][] memory m = new uint256[][](2);
        m[0] = new uint256[](2);
        m[0][0] = 11;
        m[0][1] = 22;
        m[1] = new uint256[](1);
        m[1][0] = 33;
        target.setGrid(m);
        require(target.gridAt(0, 0) == 11, "grid00");
        require(target.gridAt(0, 1) == 22, "grid01");
        require(target.gridAt(1, 0) == 33, "grid10");
    }

    function testNestedStructArrayMemoryToStorage() public {
        StructArrayCopyHarnessTarget.S[][] memory m =
            new StructArrayCopyHarnessTarget.S[][](1);
        m[0] = new StructArrayCopyHarnessTarget.S[](2);
        m[0][0] = StructArrayCopyHarnessTarget.S(7);
        m[0][1] = StructArrayCopyHarnessTarget.S(9);
        target.setNested(m);
        require(target.nestedAt(0, 0) == 7, "nested00");
        require(target.nestedAt(0, 1) == 9, "nested01");
    }

    function testTopLevelStructMemoryToStorage() public {
        StructArrayCopyHarnessTarget.S memory m = StructArrayCopyHarnessTarget.S(42);
        target.setOne(m);
        require(target.oneValue() == 42, "oneValue");
    }
}
