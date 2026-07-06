// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MulmodSignedModulus {
    function bad(int256 modulus) external pure returns (uint256) {
        return mulmod(1, 2, modulus);
    }
}
