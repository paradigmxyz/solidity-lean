// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StateShadowBase {
    uint256 internal value;
}

contract StateVariableShadowsInheritedState is StateShadowBase {
    uint256 value;
}
