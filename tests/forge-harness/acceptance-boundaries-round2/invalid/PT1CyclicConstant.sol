// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

// PT1 (2026-07-08): a `constant` whose value cyclically depends on itself (here
// mutually, A -> B -> A) is rejected by solc's
// ConstStateVarCircularReferenceChecker (PostTypeChecker.cpp:154-245, error
// 6161 "The value of the constant ... has a cyclic dependency via ...").
contract PT1CyclicConstant {
    uint256 constant A = B;
    uint256 constant B = A;
}
