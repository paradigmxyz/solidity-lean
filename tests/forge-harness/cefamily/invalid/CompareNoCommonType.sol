// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CE-6a: 1/2 (fractional, mobile ufixed) and 1 (mobile uint) share no common
// type, so the comparison is a type error (yet 1/2 == 0.5 is accepted).
contract CompareNoCommonType {
    bool public constant BAD = 1 / 2 < 1;
}
