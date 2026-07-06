// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/AddressValueConversions.sol";

contract AddressValueConversionsForgeTest {
    AddressValueConversions private target;

    function setUp() public {
        target = new AddressValueConversions();
    }

    function testAddressAndBytes20Conversions() public view {
        address input = address(0x1234);
        bytes20 expected = bytes20(hex"0000000000000000000000000000000000001234");

        require(target.addressToBytes20(input) == expected);
        require(target.bytes20ToAddress(expected) == input);
        require(target.bytes20RoundTrip(input) == input);
    }

    function testAddressAndUint160Conversions() public view {
        address input = address(0x5678);

        require(target.addressToUint160(input) == 0x5678);
        require(target.uint160ToAddress(0x5678) == input);
        require(target.uint160RoundTrip(input) == input);
    }
}
