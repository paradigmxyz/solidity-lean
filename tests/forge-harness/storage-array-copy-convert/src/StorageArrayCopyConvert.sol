// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// G14 — copy assignment INTO a DYNAMIC storage array whose element type is an
// implicitly-convertible (wider) unsigned integer and/or whose source length
// differs. solc accepts these (ArrayType::isImplicitlyConvertibleTo,
// Types.cpp:1640-1648): the dest is resized to the source length, elements are
// copied with per-element implicit conversion, and a longer old tail is zeroed
// (clearStorageRange). Solidus formerly over-rejected the whole family
// (canImplicitlyConvert had no array arm).
contract StorageArrayCopyConvertHarnessTarget {
    uint8[]   srcU8;
    uint16[]  dstU16;
    uint256[] dstU256;
    uint256[] dstDyn;

    // uint8[] -> uint16[]: element widening, dynamic dest, same length.
    function widenU8toU16() external returns (uint256, uint256, uint256) {
        srcU8.push(255);
        srcU8.push(7);
        dstU16 = srcU8;
        return (dstU16[0], dstU16[1], dstU16.length);
    }

    // uint8[] -> uint256[]: widening to the full word, longer source.
    function widenU8toU256() external returns (uint256, uint256, uint256, uint256) {
        srcU8.push(1);
        srcU8.push(2);
        srcU8.push(3);
        dstU256 = srcU8;
        return (dstU256[0], dstU256[1], dstU256[2], dstU256.length);
    }

    // Dynamic dest longer than source: resized down, old tail cleared. Regrow to
    // observe the previously-set slots came back as zero (not stale).
    function shorterClearsTail() external returns (uint256, uint256, uint256) {
        dstDyn.push(11); dstDyn.push(22); dstDyn.push(33);
        dstDyn.push(44); dstDyn.push(55);            // length 5
        srcU8.push(1); srcU8.push(2);                // uint8[] length 2
        dstDyn = srcU8;                               // -> length 2, tail cleared
        uint256 len = dstDyn.length;
        dstDyn.push(0); dstDyn.push(0); dstDyn.push(0); // regrow to indices 2..4
        return (len, dstDyn[2], dstDyn[4]);           // expect (2, 0, 0)
    }
}
