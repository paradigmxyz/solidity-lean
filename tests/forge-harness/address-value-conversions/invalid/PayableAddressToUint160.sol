// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PayableAddressToUint160 {
    function convert(address payable input)
        external
        pure
        returns (uint160)
    {
        return uint160(input);
    }
}
