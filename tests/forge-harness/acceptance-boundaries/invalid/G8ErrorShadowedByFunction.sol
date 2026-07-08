// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
// G8 — a free error E shadowed by a contract FUNCTION E. `revert E(1)` resolves
// to the (non-error) function, which solc rejects ("Expression has to be an
// error.").
error E(uint256 x);
contract G8Fn {
    function E(uint256 x) internal pure returns (uint256) { return x; }
    function f() public pure { revert E(1); }
}
