// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// solc 0.8.35 LEGACY codegen REJECTS: copying a dynamic MEMORY array whose
// element is a struct into a storage array (ArrayUtils.cpp:80-84,
// "Copying of type struct C.S memory[] memory to storage is not supported in
// legacy (only supported by the IR pipeline)").
contract DynStructMemToStorage {
    struct S {
        uint256 a;
    }

    S[] d;

    function f(S[] memory m) public {
        d = m;
    }
}
