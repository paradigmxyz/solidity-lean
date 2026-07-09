// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {CeFamilyHarnessTarget} from "../src/CeFamily.sol";

// Reads each public `constant` getter and pins solc's folded value on the EVM.
// Every getter is a CE-family over-reject / non-termination regression guard.
contract CeFamilyForgeTest {
    CeFamilyHarnessTarget private target = new CeFamilyHarnessTarget();

    function testNegativeExponents() public view {
        require(target.P1() == 2, "P1");
        require(target.P17() == 4, "P17");
        require(target.P2() == 0, "P2");
    }

    function testUnaryBitNot() public view {
        require(target.P10() == -6, "P10");
        require(target.P15() == 2, "P15");
        require(target.X250() == 250, "X250");
    }

    function testNegativeShiftsBitwise() public view {
        require(target.P6() == -4, "P6");
        require(target.P7() == -4, "P7");
        require(target.P8() == -1, "P8");
        require(target.P12() == -3, "P12");
    }

    function testFractionalModAndDenomination() public view {
        require(target.P9() == 2, "P9");
        require(target.P14() == 1, "P14");
    }

    function testBaseExemptExponents() public view {
        require(target.P5() == 1, "P5");
        require(target.PZP() == 0, "PZP");
        require(target.PNP() == 1, "PNP");
    }
}
