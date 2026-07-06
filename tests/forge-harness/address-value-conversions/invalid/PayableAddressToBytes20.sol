// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PayableAddressToBytes20 {
    function convert(address payable input)
        external
        pure
        returns (bytes20)
    {
        return bytes20(input);
    }
}
