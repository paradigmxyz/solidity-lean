// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {RationalConstantsHarnessTarget} from "../src/RationalConstants.sol";

// Reads each public `constant` getter and pins solc's folded value on the EVM.
// The negative getters are the A1 over-reject regression guards.
contract RationalConstantsForgeTest {
    RationalConstantsHarnessTarget private target =
        new RationalConstantsHarnessTarget();

    function testFractionalIntermediatesFoldExact() public view {
        require(target.F_ETHER3() == 1e18, "F_ETHER3");
        require(target.F_7_2_2() == 7, "F_7_2_2");
        require(target.M_HALFSUM() == 1, "M_HALFSUM");
    }

    function testNegativeFolding() public view {
        require(target.N_NEG5() == -5, "N_NEG5");
        require(target.N_SUB() == -7, "N_SUB");
        require(target.N_FRACNEG() == -93, "N_FRACNEG");
        require(target.N_UNARY() == -3, "N_UNARY");
    }

    function testFitBoundary() public view {
        require(target.B_U8_255() == 255, "B_U8_255");
        require(target.B_I8_MIN() == -128, "B_I8_MIN");
    }
}
