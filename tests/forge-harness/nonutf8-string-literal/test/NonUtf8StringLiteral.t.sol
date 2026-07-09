// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/NonUtf8StringLiteral.sol";

contract NonUtf8StringLiteralForgeTest {
    NonUtf8StringLiteral private target;

    function setUp() public {
        target = new NonUtf8StringLiteral();
    }

    function testLength() public view {
        // 0xFF, 0x00, 0x41 -> exactly 3 bytes (no UTF-8 re-encoding).
        require(target.convLength() == 3, "nonutf8 length");
    }

    function testConvBytes() public view {
        require(target.convByteAt(0) == 0xFF, "byte0");
        require(target.convByteAt(1) == 0x00, "byte1");
        require(target.convByteAt(2) == 0x41, "byte2");
    }

    function testAssignBytes() public view {
        // Assigning the same invalid-UTF-8 literal to a `bytes memory` local
        // yields the identical bytes.
        require(target.assignByteAt(0) == 0xFF, "assign byte0");
        require(target.assignByteAt(1) == 0x00, "assign byte1");
        require(target.assignByteAt(2) == 0x41, "assign byte2");
    }

    function testHash() public view {
        bytes32 expected = keccak256(hex"ff0041");
        require(target.convHash() == expected, "keccak of bytes");
        require(
            expected ==
                0x8713df5144a9a15c25fa20d963c79dfb5011c89f220a8a5aa20f56b444a5febc,
            "pinned keccak"
        );
    }
}
