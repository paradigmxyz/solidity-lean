// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
// Over-accept guard: INCOMPATIBLE types. `using L for uint256` + `f(bytes32 self)`.
// uint256 is not convertible to bytes32 — solc REJECTS.
library L { function f(bytes32 self) internal pure returns (bytes32) { return self; } }
contract C {
    using L for uint256;
    function g(uint256 x) external pure returns (bytes32) { return x.f(); }
}
