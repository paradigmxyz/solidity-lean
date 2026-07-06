// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

type Wad is fixed128x18;

contract FixedPointBoundary {
    mapping(fixed128x18 => uint256) private rates;
    ufixed128x18 private plain;

    function unusedLocal() external pure returns (uint256) {
        fixed128x18 x;
        return 1;
    }
}
