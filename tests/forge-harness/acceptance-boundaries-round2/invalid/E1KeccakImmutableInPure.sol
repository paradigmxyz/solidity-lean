// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

// E1 (2026-07-08): reading an immutable whose initializer is NOT a
// RationalNumber constant (here `keccak256(...)`) inside a `pure` function is a
// state-mutability violation. solc ViewPureChecker.cpp:194-199 classifies the
// read as `View` (only a RationalNumber initializer is Pure), so this is
// TypeError 2527 "Function declared as pure, but this expression (potentially)
// reads from the environment or state and thus requires view".
contract E1KeccakImmutableInPure {
    bytes32 immutable H = keccak256("x");

    function f() public pure returns (bytes32) {
        return H;
    }
}
