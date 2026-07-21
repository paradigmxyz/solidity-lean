// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {LibraryOverloadEnumArgHarnessTarget} from "../src/LibraryOverloadEnumArg.sol";

contract LibraryOverloadEnumArgForgeTest {
    LibraryOverloadEnumArgHarnessTarget private target =
        new LibraryOverloadEnumArgHarnessTarget();

    function testEnumLiteralOverload() public view {
        require(target.enumLiteralOverload() == 2, "enum literal must bind f(E)");
    }

    function testUintOverload() public view {
        require(target.uintOverload(3) == 1, "uint8 arg must bind f(uint8)");
    }

    function testConvOverload() public view {
        require(target.convOverload(1) == 2, "enum conversion must bind f(E)");
    }

    function testSingleCandidateOff() public view {
        require(target.singleCandidate(0), "isOff(E(0)) should be true");
    }

    function testSingleCandidateOn() public view {
        require(!target.singleCandidate(1), "isOff(E(1)) should be false");
    }

    function testTwoArgUint() public view {
        require(target.twoArgUint(40, 2) == 42, "g(uint256,uint8) must bind");
    }

    function testTwoArgEnum() public view {
        require(target.twoArgEnum(4) == 401, "g(uint256,E) must bind");
    }
}
