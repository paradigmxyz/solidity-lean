// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/NestedConversionLowering.sol";

contract NestedConversionLoweringForgeTest {
    NestedConversionLowering private target;

    function setUp() public {
        target = new NestedConversionLowering();
        target.seed();
    }

    function testMemoryElementConversions() public view {
        require(target.memElemLength() == 2);
        require(target.memElemEmptyFlag() == 1);
        require(target.keccakBytesElemMatch() == 1);
    }

    function testStorageNestedConversion() public view {
        require(target.storageNestedLength() == 5);
        require(target.storageNestedIndependent() == 1);
    }

    function testMemoryAliasThroughConversion() public view {
        require(target.memAliasThroughConv() == 1);
    }
}
