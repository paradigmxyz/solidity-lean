// SPDX-License-Identifier: BSD-3-Clause
pragma solidity ^0.8.20;

import {CompoundExponentialNoErrorHarness} from "../src/CompoundExponentialNoError.sol";

contract CompoundExponentialNoErrorForgeTest {
    uint256 private constant EXP_SCALE = 1e18;
    uint256 private constant DOUBLE_SCALE = 1e36;

    function _call(address target, bytes memory payload)
        private
        returns (bool ok, bytes memory result)
    {
        (ok, result) = target.call(payload);
    }

    function testScalarAndComparisons() public {
        CompoundExponentialNoErrorHarness harness =
            new CompoundExponentialNoErrorHarness();

        (
            uint256 truncated,
            uint256 scaled,
            uint256 scaledPlus
        ) = harness.scalarSummary(125 * EXP_SCALE / 100, 4, 7);
        require(truncated == 1, "truncated");
        require(scaled == 5, "scaled");
        require(scaledPlus == 12, "scaledPlus");

        (
            bool less,
            bool lessOrEqual,
            bool greater,
            bool zeroValue
        ) = harness.compareSummary(2 * EXP_SCALE, 3 * EXP_SCALE);
        require(less, "less");
        require(lessOrEqual, "lessOrEqual");
        require(greater, "greater");
        require(zeroValue, "zero");
    }

    function testExpArithmeticOverloads() public {
        CompoundExponentialNoErrorHarness harness =
            new CompoundExponentialNoErrorHarness();

        (
            uint256 added,
            uint256 subtracted,
            uint256 multiplied,
            uint256 divided
        ) = harness.expArithmetic(2 * EXP_SCALE, 3 * EXP_SCALE);

        require(added == 5 * EXP_SCALE, "exp added");
        require(subtracted == EXP_SCALE, "exp subtracted");
        require(multiplied == 6 * EXP_SCALE, "exp multiplied");
        require(divided == 15 * EXP_SCALE / 10, "exp divided");

        (
            uint256 scalarProduct,
            uint256 uintTimesExp
        ) = harness.expScalarProducts(2 * EXP_SCALE, 4);
        require(scalarProduct == 8 * EXP_SCALE, "exp scalar product");
        require(uintTimesExp == 8, "uint times exp");
    }

    function testDoubleArithmeticAndFraction() public {
        CompoundExponentialNoErrorHarness harness =
            new CompoundExponentialNoErrorHarness();

        (
            uint256 added,
            uint256 subtracted,
            uint256 multiplied,
            uint256 divided
        ) = harness.doubleArithmetic(2 * DOUBLE_SCALE, 3 * DOUBLE_SCALE);

        require(added == 5 * DOUBLE_SCALE, "double added");
        require(subtracted == DOUBLE_SCALE, "double subtracted");
        require(multiplied == 6 * DOUBLE_SCALE, "double multiplied");
        require(divided == 15 * DOUBLE_SCALE / 10, "double divided");

        (
            uint256 scalarProduct,
            uint256 uintTimesDouble
        ) = harness.doubleScalarProducts(2 * DOUBLE_SCALE, 4);
        require(scalarProduct == 8 * DOUBLE_SCALE, "double scalar product");
        require(uintTimesDouble == 8, "uint times double");
        require(
            harness.fractionMantissa(7, 2) == 35 * DOUBLE_SCALE / 10,
            "fraction"
        );
    }

    function testSafeDowncastsAndReverts() public {
        CompoundExponentialNoErrorHarness harness =
            new CompoundExponentialNoErrorHarness();

        (uint224 as224, uint32 as32) = harness.safeDowncastSummary(42);
        require(as224 == uint224(42), "as224");
        require(as32 == uint32(42), "as32");

        (bool overflow224, ) = _call(
            address(harness),
            abi.encodeWithSelector(harness.safe224Public.selector, 2 ** 224)
        );
        require(!overflow224, "overflow224");

        (bool overflow32, ) = _call(
            address(harness),
            abi.encodeWithSelector(harness.safe32Public.selector, 2 ** 32)
        );
        require(!overflow32, "overflow32");
    }
}
