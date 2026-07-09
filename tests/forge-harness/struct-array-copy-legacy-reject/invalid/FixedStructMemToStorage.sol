// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// solc 0.8.35 LEGACY codegen REJECTS: copying a FIXED-size MEMORY array whose
// element is a struct into a storage array. Fixed vs dynamic source does not
// matter for the struct-element (non-array base) branch — the reject fires the
// same way (ArrayUtils.cpp:80-84).
contract FixedStructMemToStorage {
    struct S {
        uint256 a;
    }

    S[] d;

    function f(S[2] memory m) public {
        d = m;
    }
}
