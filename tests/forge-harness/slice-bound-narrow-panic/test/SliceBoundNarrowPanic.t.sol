// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import "../src/SliceBoundNarrowPanic.sol";

contract SliceBoundNarrowPanicForgeTest {
    SliceBoundNarrowPanicHarnessTarget private target;

    function setUp() public {
        target = new SliceBoundNarrowPanicHarnessTarget();
    }

    function assertPanic11(bool ok, bytes memory ret, string memory label)
        internal
        pure
    {
        require(!ok, label);
        require(ret.length == 36, "Panic(0x11) returndata length");
        require(
            keccak256(ret)
                == keccak256(
                    abi.encodeWithSignature("Panic(uint256)", uint256(0x11))
                ),
            "must be Panic(0x11)"
        );
    }

    // uint8 200 + 100 overflows at its own width -> Panic(0x11), NOT the
    // slice's empty bounds revert.
    function testStartBoundOverflowPanic11() public {
        (bool ok, bytes memory ret) = address(target).call(
            abi.encodeWithSignature(
                "go(uint8,uint8)", uint8(200), uint8(100)
            )
        );
        assertPanic11(ok, ret, "go(200,100) should revert");
    }

    // In-range control: msg.data is 4 + 64 = 68 bytes; [3:] leaves 65.
    function testStartBoundInRangeControl() public view {
        uint256 len = target.go(1, 2);
        require(len == 65, "go(1,2) slice length");
    }

    // Stop-bound `[:a+b]` overflow -> Panic(0x11).
    function testStopBoundOverflowPanic11() public {
        (bool ok, bytes memory ret) = address(target).call(
            abi.encodeWithSignature(
                "goStop(uint8,uint8)", uint8(200), uint8(100)
            )
        );
        assertPanic11(ok, ret, "goStop(200,100) should revert");
    }

    function testStopBoundInRangeControl() public view {
        uint256 len = target.goStop(1, 2);
        require(len == 3, "goStop(1,2) slice length");
    }

    // Both-bounds `[a:a+b]` overflow in the stop bound -> Panic(0x11).
    function testBothBoundsOverflowPanic11() public {
        bytes memory data =
            hex"0102030405060708090a"; // 10 bytes
        (bool ok, bytes memory ret) = address(target).call(
            abi.encodeWithSignature(
                "goBoth(bytes,uint8,uint8)", data, uint8(200), uint8(100)
            )
        );
        assertPanic11(ok, ret, "goBoth(200,100) should revert");
    }

    function testBothBoundsInRangeControl() public view {
        bytes memory data = hex"0102030405060708090a";
        uint256 len = target.goBoth(data, 2, 3);
        require(len == 3, "goBoth(data,2,3) slice length");
    }
}
