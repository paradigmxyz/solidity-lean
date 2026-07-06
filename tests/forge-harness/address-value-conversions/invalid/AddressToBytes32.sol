// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract AddressToBytes32 {
    function convert(address input) external pure returns (bytes32) {
        return bytes32(input);
    }
}
