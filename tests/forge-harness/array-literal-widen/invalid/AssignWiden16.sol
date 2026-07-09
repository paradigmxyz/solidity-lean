// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// uint8[3] ↛ uint16[3]: element widening for a fixed array is disallowed.
contract AssignWiden16 {
    function f() public pure {
        uint16[3] memory x = [1, 2, 3];
        x;
    }
}
