// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Item #1: solc packs narrow value-type array elements floor(32/size) per slot
// and NEVER lets an element straddle a slot boundary. uint72 (9 bytes) -> 3 per
// slot, so uint72[7] spans 3 slots and element 3 starts a fresh slot; uint96
// (12 bytes) -> 2 per slot; bytes3 (3 bytes) -> 10 per slot. A round-trip
// through storage detects both the wrong per-element offset and the wrong slot
// count (which would otherwise clobber the trailing `sentinel`).
contract StorageArrayPackingTarget {
    uint72[7] a;
    uint96[] b;
    bytes3[] c;
    uint256 sentinel;

    function setup() external {
        for (uint256 i = 0; i < 7; i++) {
            a[i] = uint72(0x11 * (i + 1));
        }
        for (uint256 i = 0; i < 5; i++) {
            b.push(uint96(0x22 * (i + 1)));
        }
        for (uint256 i = 0; i < 5; i++) {
            c.push(bytes3(uint24(0x33 * (i + 1))));
        }
        sentinel = 0xdeadbeef;
    }

    function getA(uint256 i) external view returns (uint72) { return a[i]; }
    function getB(uint256 i) external view returns (uint96) { return b[i]; }
    function getC(uint256 i) external view returns (bytes3) { return c[i]; }
    function getSentinel() external view returns (uint256) { return sentinel; }
}
