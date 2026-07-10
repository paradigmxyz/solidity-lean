// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
// Over-accept guard: SIGNEDNESS mismatch. `using L for int8` + `f(uint256 self)`.
// int8 is not implicitly convertible to uint256 — solc REJECTS.
library L { function f(uint256 self) internal pure returns (uint256) { return self; } }
contract C {
    using L for int8;
    function g(int8 x) external pure returns (uint256) { return x.f(); }
}
