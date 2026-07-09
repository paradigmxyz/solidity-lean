// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/TernaryBytesNCommonType.sol";

contract TernaryBytesNCommonTypeForgeTest {
    TernaryBytesNCommonType private target;

    bytes4 private constant X = 0x11223344;
    bytes2 private constant Y = 0xaabb;

    function setUp() public {
        target = new TernaryBytesNCommonType();
    }

    // else-branch: bytes2 0xaabb widened to bytes4 lands in the HIGH bytes.
    function testReturnElseWidensLeftAligned() public view {
        require(
            target.f(false, X, Y) == bytes4(0xaabb0000),
            "else branch widens left-aligned"
        );
    }

    function testReturnThenUnchanged() public view {
        require(target.f(true, X, Y) == X, "then branch unchanged");
    }

    function testEncodeElseWidensLeftAligned() public view {
        require(
            keccak256(target.enc(false, X, Y)) ==
                keccak256(abi.encode(bytes4(0xaabb0000))),
            "abi.encode else branch"
        );
    }

    function testPackedElseWidensLeftAligned() public view {
        require(
            keccak256(target.packed(false, X, Y)) ==
                keccak256(abi.encodePacked(bytes4(0xaabb0000))),
            "abi.encodePacked else branch"
        );
        require(
            target.packed(false, X, Y).length == 4,
            "packed length is common-type width"
        );
    }

    // Integer control: widening a narrow int branch is a value no-op.
    function testIntegerControlThen() public view {
        require(target.g(true, 0x11, 7) == 0x11, "int then branch");
    }

    function testIntegerControlElse() public view {
        require(target.g(false, 0x11, 7) == 7, "int else branch");
    }
}
