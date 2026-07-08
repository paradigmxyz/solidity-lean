// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

// O1 (2026-07-08): a duplicate contract in an override(...) list is rejected by
// solc OverrideChecker.cpp:850-879 (error 4520 "Duplicate contract ... found in
// override list").
contract A { function f() public virtual {} }
contract B { function f() public virtual {} }

contract O1DuplicateOverride is A, B {
    function f() public override(A, A) {}
}
