// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main {
    uint8 s;
    function word() internal view returns (bytes2) { return bytes2(uint16(s)); }
    function pick() internal returns (uint256) { s = 7; return 1; }
    function f(uint8 x) external returns (bytes1) { s = x; return word()[pick()]; }
}
