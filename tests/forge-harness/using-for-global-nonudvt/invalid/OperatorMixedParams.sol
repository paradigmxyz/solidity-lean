// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// UF2 reject: an operator function must have BOTH parameters exactly the target
// type. `addMixed(T, uint256)` bound as `+` is rejected (1884 "Wrong parameters
// in operator definition. The function needs to have two parameters of type T").

type T is uint256;

function addMixed(T a, uint256 b) pure returns (T) {
    return a;
}

using {addMixed as +} for T global;

contract OperatorMixedParams {}
