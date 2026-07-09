// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// solc rejects a signed/negative exponent for `**` (exponent must be unsigned).
contract NegativeExponent {
    function bad(int256 b) external pure returns (int256) {
        return b ** (-1);
    }
}
