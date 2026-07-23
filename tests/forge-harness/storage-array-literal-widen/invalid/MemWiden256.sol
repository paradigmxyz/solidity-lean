// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// MEMORY twin of the accepted storage `uint256[2] arr = [50,0]`. solc types
// `[50,0]` as uint8[2]; uint8[2] is NOT implicitly convertible to a uint256[2]
// MEMORY target (no fixed-array element widening for memory). solc REJECTS.
contract MemWiden256 {
    function f() public pure {
        uint256[2] memory x = [50, 0];
        x;
    }
}
