// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
// G8 — a free error E shadowed by a contract STATE VAR E. `revert E(1)` is a
// revert of a non-callable, which solc rejects ("This expression is not
// callable.").
error E(uint256 x);
contract G8State {
    uint256 E;
    function f() public { revert E(1); }
}
