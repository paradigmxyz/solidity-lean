// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.20;

import {UniswapV3MathHarness} from "../src/UniswapV3Math.sol";

contract UniswapV3MathForgeTest {
    function testBitMathMostAndLeastSignificantBits() public {
        UniswapV3MathHarness target = new UniswapV3MathHarness();

        require(target.mostSignificantBit(1) == 0, "msb 1");
        require(target.mostSignificantBit(2) == 1, "msb 2");
        require(target.mostSignificantBit(255) == 7, "msb 255");
        require(target.mostSignificantBit(1 << 128) == 128, "msb 128");
        require(target.mostSignificantBit(type(uint256).max) == 255, "msb max");

        require(target.leastSignificantBit(1) == 0, "lsb 1");
        require(target.leastSignificantBit(2) == 1, "lsb 2");
        require(target.leastSignificantBit(0x100) == 8, "lsb 8");
        require(target.leastSignificantBit(1 << 128) == 128, "lsb 128");
        require(target.leastSignificantBit(type(uint256).max) == 0, "lsb max");
    }

    function testBitMathZeroReverts() public {
        UniswapV3MathHarness target = new UniswapV3MathHarness();

        try target.mostSignificantBit(0) returns (uint8) {
            revert("expected msb revert");
        } catch {}

        try target.leastSignificantBit(0) returns (uint8) {
            revert("expected lsb revert");
        } catch {}
    }

    function testTickMathConstantsAndKnownRatios() public {
        UniswapV3MathHarness target = new UniswapV3MathHarness();

        require(target.minTick() == -887272, "min tick");
        require(target.maxTick() == 887272, "max tick");
        require(target.minSqrtRatio() == 4295128739, "min sqrt");
        require(
            target.maxSqrtRatio() ==
                1461446703485210103287273052203988822378723970342,
            "max sqrt"
        );

        require(target.sqrtRatioAtTick(0) == 79228162514264337593543950336, "tick 0");
        require(target.sqrtRatioAtTick(1) == 79232123823359799118286999568, "tick 1");
        require(target.sqrtRatioAtTick(-1) == 79224201403219477170569942574, "tick -1");
        require(target.sqrtRatioAtTick(-887272) == 4295128739, "tick min");
        require(
            target.sqrtRatioAtTick(887272) ==
                1461446703485210103287273052203988822378723970342,
            "tick max"
        );
    }

    function testTickMathBoundsRevert() public {
        UniswapV3MathHarness target = new UniswapV3MathHarness();

        try target.sqrtRatioAtTick(887273) returns (uint160) {
            revert("expected high tick revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) == keccak256(bytes("T")),
                "high reason"
            );
        }

        try target.sqrtRatioAtTick(-887273) returns (uint160) {
            revert("expected low tick revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) == keccak256(bytes("T")),
                "low reason"
            );
        }
    }
}
