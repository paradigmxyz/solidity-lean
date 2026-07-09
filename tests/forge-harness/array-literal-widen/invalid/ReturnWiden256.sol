// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// returning uint8[3] literal as uint256[3] — element widening disallowed.
contract ReturnWiden256 {
    function f() public pure returns (uint256[3] memory) {
        return [1, 2, 3];
    }
}
