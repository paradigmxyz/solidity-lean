// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// UF1 reject neighbor: `global` on a built-in / elementary type is rejected
// (8841 "Can only use \"global\" with user-defined types."). Loosening the gate
// to admit struct/enum/UDVT must NOT admit a built-in target.

function identity(uint256 x) pure returns (uint256) {
    return x;
}

using {identity} for uint256 global;

contract BuiltinTargetGlobal {}
