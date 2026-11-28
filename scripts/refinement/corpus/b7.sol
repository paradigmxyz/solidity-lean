// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main {
    uint8[] v;
    function push() internal returns (uint8) { v.push(7); return 1; }
    function pair() internal returns (uint8[] memory, uint8) { return (v, push()); }
    function f(bool b) external returns (uint256) {
        delete v;
        if (b) {
            (uint8[] memory c, uint8 m) = pair();
            return c.length + m;
        }
        return v.length;
    }
}
