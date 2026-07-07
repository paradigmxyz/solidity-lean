// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract Packing {
    // slot 0: packed a(uint8) b(uint16) c(bool) d(address) e(uint8)
    uint8 a;
    uint16 b;
    bool c;
    address d;
    uint8 e;

    function setAll(uint8 _a, uint16 _b, bool _c, address _d, uint8 _e) external {
        a = _a; b = _b; c = _c; d = _d; e = _e;
    }
    function setA(uint8 _a) external { a = _a; }
    function setE(uint8 _e) external { e = _e; }
    function getA() external view returns (uint8) { return a; }
    function getB() external view returns (uint16) { return b; }
    function getC() external view returns (bool) { return c; }
    function getD() external view returns (address) { return d; }
    function getE() external view returns (uint8) { return e; }
}
