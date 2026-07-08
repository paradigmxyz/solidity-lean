// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
contract C {
    uint256[] xs;
    function req() internal pure { require(false, "x"); }
    function pick(bool c) internal returns (uint256[] storage p) {
        if (c) { p = xs; return p; }
        req();
    }
}
