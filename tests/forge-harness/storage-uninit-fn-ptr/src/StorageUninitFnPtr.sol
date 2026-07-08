// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// G17 pin (docs/solidus-solc-deep-comparison.md): an internal function pointer
// held in a STORAGE state variable that is never assigned has the zero dispatch
// value; calling it panics 0x51 (Panic: invalid internal function). This is the
// storage-default counterpart of the already-laned LOCAL-uninitialized pointer
// call (internal-fn-pointers `callUninitialized`). A constructor path that also
// leaves the pointer unset behaves identically. Every probe is self-contained.
contract StorageUninitFnPtrHarnessTarget {
    // Never assigned anywhere: default (zero) internal function pointer.
    function(uint256) internal pure returns (uint256) storedFn;

    // A second pointer only ever set on a branch the constructor does not take,
    // so it is likewise left at its zero default.
    function(uint256) internal pure returns (uint256) ctorFn;

    function dbl(uint256 x) internal pure returns (uint256) {
        return 2 * x;
    }

    constructor(bool assign) {
        if (assign) {
            // Dead branch for our probes (we deploy with assign = false), so the
            // pointer stays at its zero default and calling it later panics.
            ctorFn = dbl;
        }
    }

    // Calling the never-assigned storage pointer panics 0x51.
    function callStored(uint256 x) public view returns (uint256) {
        return storedFn(x);
    }

    // Calling the constructor-left-unset storage pointer panics 0x51.
    function callCtor(uint256 x) public view returns (uint256) {
        return ctorFn(x);
    }
}
