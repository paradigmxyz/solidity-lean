// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// solc 0.8.35 LEGACY codegen REJECTS: copying a CALLDATA array whose element is
// a struct into a storage array (ArrayUtils.cpp:80-84, with `fromMemoryOrCalldata`
// covering the calldata source too).
contract StructCalldataToStorage {
    struct S {
        uint256 a;
    }

    S[] d;

    function f(S[] calldata m) external {
        d = m;
    }
}
