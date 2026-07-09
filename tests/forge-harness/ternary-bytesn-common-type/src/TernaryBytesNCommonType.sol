// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A conditional `c ? x : y` whose branches are `bytesN` of DIFFERENT widths
// takes the ternary's COMMON type (the wider `bytesN`). solc inserts the
// implicit `convert_t_bytesM_to_t_bytesN` on the narrower branch. Because
// `bytesN` is LEFT-aligned, widening `bytes2 0xaabb` to `bytes4` keeps the
// content in the HIGH bytes -> `0xaabb0000`, NOT `0x0000aabb`.
//
// The integer control `g` locks in that integer branches are unaffected:
// narrow ints are stored sign/zero-extended, so widening is a value no-op.
contract TernaryBytesNCommonType {
    function f(bool c, bytes4 x, bytes2 y) external pure returns (bytes4) {
        return c ? x : y; // common type bytes4
    }

    function enc(bool c, bytes4 x, bytes2 y) external pure returns (bytes memory) {
        return abi.encode(c ? x : y);
    }

    function packed(bool c, bytes4 x, bytes2 y)
        external
        pure
        returns (bytes memory)
    {
        return abi.encodePacked(c ? x : y);
    }

    // Integer-ternary control: common type uint256; a narrow uint8 branch is
    // stored zero-extended so widening is a no-op -> must remain correct.
    function g(bool c, uint8 a, uint256 b) external pure returns (uint256) {
        return c ? a : b;
    }
}
