// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {OpenZeppelinSignedMathHarness} from "../src/OpenZeppelinSignedMath.sol";

contract OpenZeppelinSignedMathForgeTest {
    function testMaxMinAndTernary() public {
        OpenZeppelinSignedMathHarness target =
            new OpenZeppelinSignedMathHarness();

        require(target.max(-4, 7) == 7, "max mixed");
        require(target.max(-9, -3) == -3, "max negative");
        require(target.min(-4, 7) == -4, "min mixed");
        require(target.min(-9, -3) == -9, "min negative");
        require(target.ternary(true, -11, 22) == -11, "ternary true");
        require(target.ternary(false, -11, 22) == 22, "ternary false");
    }

    function testAverageRoundsTowardZero() public {
        OpenZeppelinSignedMathHarness target =
            new OpenZeppelinSignedMathHarness();

        require(target.average(5, 2) == 3, "positive average");
        require(target.average(-5, -2) == -3, "negative average");
        require(target.average(-5, 2) == -1, "mixed average");
        require(
            target.average(type(int256).max, type(int256).max) ==
                type(int256).max,
            "max average"
        );
        require(
            target.average(type(int256).min, type(int256).min) ==
                type(int256).min,
            "min average"
        );
    }

    function testAbsIncludingMinInt() public {
        OpenZeppelinSignedMathHarness target =
            new OpenZeppelinSignedMathHarness();

        require(target.abs(0) == 0, "abs zero");
        require(target.abs(42) == 42, "abs positive");
        require(target.abs(-42) == 42, "abs negative");
        require(
            target.abs(type(int256).min) ==
                uint256(type(int256).max) + 1,
            "abs min"
        );
    }

    function testSummary() public {
        OpenZeppelinSignedMathHarness target =
            new OpenZeppelinSignedMathHarness();

        (
            int256 high,
            int256 low,
            int256 mean,
            uint256 absA,
            uint256 absB
        ) = target.summary(-12, 5);

        require(high == 5, "summary high");
        require(low == -12, "summary low");
        require(mean == -3, "summary mean");
        require(absA == 12, "summary abs a");
        require(absB == 5, "summary abs b");
    }
}
