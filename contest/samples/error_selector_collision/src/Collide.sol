// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract Entry {
    error E82926();
    function f() external pure {
        revert E82926();
    }
}

// File-level error whose 4-byte selector (0x554d5780) COLLIDES with E82926().
// Placed after Entry so a last-wins selector map resolves 0x554d5780 to THIS
// name (E94430) rather than the actually-reverted E82926 -> the EVM side would
// render custom:E94430 while solidity-lean renders custom:E82926 for BYTE-IDENTICAL
// revert data (0x554d5780, no args) that no caller can tell apart.
error E94430();
