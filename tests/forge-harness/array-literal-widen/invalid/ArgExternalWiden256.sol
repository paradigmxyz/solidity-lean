// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// passing uint8[3] literal to a uint256[3] external parameter — disallowed.
contract ArgExternalWiden256 {
    function g(uint256[3] memory a) external pure { a; }
    function f() external { this.g([1, 2, 3]); }
}
