// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// A genuinely-fractional constant into an integer type must stay REJECTED — the
// Int-widening must not over-correct into unsoundness (folding 7/2 to 3).
contract FractionalIntoInt {
    int256 public constant BAD = 7 / 2; // rational_const 7 / 2, not convertible
}
