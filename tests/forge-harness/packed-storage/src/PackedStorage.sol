// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PackedStorageHarnessTarget {
    uint8 public a;
    uint16 public b;
    bool public c;
    int8 public s;
    uint256 public d;

    struct Pair {
        uint8 a;
        uint16 b;
        bool c;
        int8 s;
        uint256 d;
    }

    Pair private pair;
    uint256 private tail;
    uint8[4] private fixeds;
    uint256 private afterFixed;

    function setTopLevel() external returns (uint256) {
        a = 0x12;
        b = 0x3456;
        c = true;
        s = -1;
        d = 9;
        return d;
    }

    function readTopLevel()
        external
        view
        returns (uint8, uint16, bool, int8, uint256)
    {
        return (a, b, c, s, d);
    }

    function setStructAndArray() external returns (uint256) {
        pair.a = 0x12;
        pair.b = 0x3456;
        pair.c = true;
        pair.s = -1;
        pair.d = 9;
        tail = 10;
        fixeds[0] = 0xaa;
        fixeds[1] = 0xbb;
        fixeds[2] = 0xcc;
        fixeds[3] = 0xdd;
        afterFixed = 11;
        return afterFixed;
    }

    function readStruct()
        external
        view
        returns (uint8, uint16, bool, int8, uint256)
    {
        return (pair.a, pair.b, pair.c, pair.s, pair.d);
    }

    function readFixeds()
        external
        view
        returns (uint8, uint8, uint8, uint8, uint256, uint256)
    {
        return (fixeds[0], fixeds[1], fixeds[2], fixeds[3], tail, afterFixed);
    }
}
