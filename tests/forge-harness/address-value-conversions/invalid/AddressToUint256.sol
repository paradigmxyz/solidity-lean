// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract AddressToUint256 {
    function convert(address input) external pure returns (uint256) {
        return uint256(input);
    }
}
