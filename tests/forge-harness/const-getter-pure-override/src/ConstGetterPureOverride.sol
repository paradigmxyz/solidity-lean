// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// CONST-GETTER-PURE-OVERRIDE (#115) — a `public constant` state variable's
// synthesized getter has state mutability PURE (not view), because a constant
// value is fixed at compile time and reads no state. solc `Types.cpp`
// `OverrideProxy::stateMutability()` returns `isConstant() ? Pure : View`, so a
// `public constant` variable CAN override a `pure` interface/base function.
// solidity-lean formerly over-rejected this (its synthesized getter was always
// `view`, and `view` cannot override `pure`).
interface I {
    function X() external pure returns (uint256);
}

contract ConstGetterPureOverrideHarnessTarget is I {
    uint256 public constant override X = 5;
}
