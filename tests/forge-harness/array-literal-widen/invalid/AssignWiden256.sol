// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// solc types `[1,2,3]` as uint8[3]; uint8[3] is NOT implicitly convertible to
// uint256[3] (fixed-array element widening is disallowed). solc rejects.
contract AssignWiden256 {
    function f() public pure {
        uint256[3] memory x = [1, 2, 3];
        x;
    }
}
