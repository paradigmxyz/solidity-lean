// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #156 LIB-STORAGE-RETURN-USE — a contract that calls an INTERNAL library
// function value-returning a `storage` struct reference and then dereferences
// the returned pointer, writing and reading state THROUGH it. solc 0.8.35
// accepts and runs this (the internal function is inlined; the returned pointer
// resolves to the caller's storage slot); the model formerly accepted it in the
// checker (#155) but could not lower the USE, over-rejecting the whole contract.
// This fixture pins the real-EVM behaviour: writing 42 through the returned ref
// and reading it back yields 42.
library L {
    struct S { uint256 x; }

    // Value-returns the storage reference it was handed (a WHOLE reference).
    function ref(S storage s) internal pure returns (S storage) {
        return s;
    }
}

contract LibStorageReturnUseHarness {
    L.S internal s;

    // Write x through the returned `S storage` ref.
    function setThrough(uint256 v) external {
        L.ref(s).x = v;
    }

    // Read x through the returned `S storage` ref.
    function getThrough() external view returns (uint256) {
        return L.ref(s).x;
    }

    // Convenience: write then read in one call (matches the Lean witness).
    function writeReadStruct(uint256 v) external returns (uint256) {
        L.ref(s).x = v;
        return L.ref(s).x;
    }
}
