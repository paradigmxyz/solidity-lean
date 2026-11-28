// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main {
    struct S { uint8[] a; uint8 m; }
    uint8[] v;
    function push() internal returns (uint8) { v.push(7); return 1; }
    function f(bool b) external returns (uint256) {
        delete v;
        if (b) {
            S memory s = S(v, push());
            return s.a.length + s.m;
        }
        return v.length;
    }
}
