// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/NumericBytesConversions.sol";

contract NumericBytesConversionsForgeTest {
    NumericBytesConversions private target;

    function setUp() public {
        target = new NumericBytesConversions();
    }

    function testIntegerWidthAndSignConversions() public view {
        require(target.uint16FromUint8(0xff) == 0xff);
        require(target.uint8FromUint16(0x12ff) == 0xff);
        require(target.uint8FromInt8(-1) == 0xff);
        require(target.int8FromUint8(0xff) == -1);
    }

    function testFixedBytesWidthConversions() public view {
        require(target.bytes4FromBytes2(0xabcd) == 0xabcd0000);
        require(target.bytes2FromBytes4(0xabcdef01) == 0xabcd);
    }

    function testFixedBytesIntegerSameWidthConversions() public view {
        require(target.bytes2FromUint16(0xabcd) == 0xabcd);
        require(target.uint16FromBytes2(0xabcd) == 0xabcd);
    }
}
