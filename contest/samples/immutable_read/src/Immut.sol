// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Differential probe: an immutable set in the constructor and read back by a
// view function. Immutables are spliced into the deployed RUNTIME bytecode (not
// read from a storage slot), a distinct codegen/read path -> f() returns 42 ->
// success|w:42. A wrong/zero value on one engine would be a fake wrong-value gap.
contract Immut {
    uint256 public immutable X;

    constructor() {
        X = 42;
    }

    function f() external view returns (uint256) {
        return X;
    }
}
