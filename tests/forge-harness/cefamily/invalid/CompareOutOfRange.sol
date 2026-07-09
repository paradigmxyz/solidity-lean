// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CE-6a: neither 2**300 nor 2**301 has an integer mobile type (both exceed the
// s256/u256 range), so the comparison has no common type.
contract CompareOutOfRange {
    bool public constant BAD = 2 ** 300 < 2 ** 301;
}
