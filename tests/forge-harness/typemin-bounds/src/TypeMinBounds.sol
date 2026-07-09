// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// TYPEMIN: `type(intN).min` for N < 256 must lower to the two's-complement
// negative word `2^256 - 2^(N-1)`, not the raw positive `2^(N-1)`. solc pushes
// `0xff..ff80` for `type(int8).min` (= -128), `0xff..ff80..00` for
// `type(int128).min` (= -2^127), and `0x80..00` for `type(int256).min`
// (= -2^255). A raw positive word would make `type(int8).min == -128` false and
// ABI-encode the wrong bytes.
contract TypeMinBounds {
    function int8Min() external pure returns (int256) {
        return type(int8).min;
    }

    function int128Min() external pure returns (int256) {
        return type(int128).min;
    }

    function int256Min() external pure returns (int256) {
        return type(int256).min;
    }

    function int8MinNarrow() external pure returns (int8) {
        return type(int8).min;
    }

    function int128MinNarrow() external pure returns (int128) {
        return type(int128).min;
    }

    function int8MinEqNeg128() external pure returns (bool) {
        return type(int8).min == -128;
    }

    function int8MinPlusOne() external pure returns (int8) {
        return type(int8).min + 1;
    }
}
