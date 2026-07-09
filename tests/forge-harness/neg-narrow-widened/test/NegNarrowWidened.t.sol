// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {NegNarrowWidenedHarnessTarget} from "../src/NegNarrowWidened.sol";

contract NegNarrowWidenedForgeTest {
    // Control: -x of a non-min int8 widens correctly (no panic).
    function testNegNoOverflow() public {
        NegNarrowWidenedHarnessTarget t = new NegNarrowWidenedHarnessTarget();
        require(t.negI8toI16(-100) == 100, "neg100");
    }
    // Control: int16(-x) of a non-min int8.
    function testCastNegNoOverflow() public {
        NegNarrowWidenedHarnessTarget t = new NegNarrowWidenedHarnessTarget();
        require(t.castNegI8toI16(-100) == 100, "cast100");
    }
    // Checked -x of int8.min widened to int16 Panics 0x11.
    function testNegMinPanics() public {
        NegNarrowWidenedHarnessTarget t = new NegNarrowWidenedHarnessTarget();
        (bool ok, bytes memory data) = address(t).call(
            abi.encodeWithSignature("negI8toI16(int8)", type(int8).min));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
    // Checked int16(-x) of int8.min Panics 0x11 (explicit-cast path).
    function testCastNegMinPanics() public {
        NegNarrowWidenedHarnessTarget t = new NegNarrowWidenedHarnessTarget();
        (bool ok, bytes memory data) = address(t).call(
            abi.encodeWithSignature("castNegI8toI16(int8)", type(int8).min));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
    // Unchecked -x of int8.min wraps to int8.min (-128), not 128.
    function testNegUncheckedWraps() public {
        NegNarrowWidenedHarnessTarget t = new NegNarrowWidenedHarnessTarget();
        require(t.negI8toI16Unchecked(type(int8).min) == -128, "wrap-128");
    }
    // Unchecked int16(-x) of int8.min wraps to -128.
    function testCastNegUncheckedWraps() public {
        NegNarrowWidenedHarnessTarget t = new NegNarrowWidenedHarnessTarget();
        require(t.castNegI8toI16Unchecked(type(int8).min) == -128, "cast-wrap-128");
    }
    // Checked -x of int128.min widened to int256 Panics 0x11.
    function testNegI128MinPanics() public {
        NegNarrowWidenedHarnessTarget t = new NegNarrowWidenedHarnessTarget();
        (bool ok, bytes memory data) = address(t).call(
            abi.encodeWithSignature("negI128toI256(int128)", type(int128).min));
        require(!ok, "should revert");
        require(data.length == 36 && data[35] == 0x11, "panic 0x11");
    }
    // Unchecked -x of int128.min wraps back to int128.min.
    function testNegI128UncheckedWraps() public {
        NegNarrowWidenedHarnessTarget t = new NegNarrowWidenedHarnessTarget();
        require(t.negI128toI256Unchecked(type(int128).min) == type(int128).min, "wrap-i128");
    }
}
