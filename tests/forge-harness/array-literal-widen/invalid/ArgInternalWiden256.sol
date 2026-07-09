// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// passing uint8[3] literal to a uint256[3] internal parameter — disallowed.
contract ArgInternalWiden256 {
    function g(uint256[3] memory a) internal pure { a; }
    function f() public pure { g([1, 2, 3]); }
}
