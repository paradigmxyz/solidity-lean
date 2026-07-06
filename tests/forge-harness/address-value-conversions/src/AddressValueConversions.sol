// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract AddressValueConversions {
    function addressToBytes20(address input)
        external
        pure
        returns (bytes20)
    {
        return bytes20(input);
    }

    function bytes20ToAddress(bytes20 input)
        external
        pure
        returns (address)
    {
        return address(input);
    }

    function addressToUint160(address input)
        external
        pure
        returns (uint160)
    {
        return uint160(input);
    }

    function uint160ToAddress(uint160 input)
        external
        pure
        returns (address)
    {
        return address(input);
    }

    function bytes20RoundTrip(address input)
        external
        pure
        returns (address)
    {
        return address(bytes20(input));
    }

    function uint160RoundTrip(address input)
        external
        pure
        returns (address)
    {
        return address(uint160(input));
    }
}
