// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main {
    uint8 x;
    modifier m(uint8 k) {
        if (k == 2) return;
        _;
        x = k;
    }
    function f(bool b) external m(b ? 1 : 3) m(2) {}
}
