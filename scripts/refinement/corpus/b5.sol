// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main {
    uint8[] v;
    function push() internal returns (uint8) { v.push(7); return 1; }
    function f(bool b) external returns (uint256) {
        delete v;
        if (b) {
            (uint8[] memory c, uint8 m) = (v, push());
            return c.length + m;
        }
        return v.length;
    }
}
