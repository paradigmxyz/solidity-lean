// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// #166 OVERLOAD-MEM-VS-STORAGE — over-reject. solc 0.8.35 treats memory and
// storage array parameters as DISTINCT overload signatures, so
// `f(uint256[] memory)` and `f(uint256[] storage)` may coexist. The model
// REJECTED the declaration with TypeError.duplicateSignature "f":
// `FunctionSig.sameSignature` compared only the name and the `Ty` list, and both
// params lower to `Ty.array (Ty.uint 256) none`, so the data location was
// ignored. solc's duplicate check normalizes only CallData->Memory
// (asExternallyCallableFunction) and compares location-aware, so memory ==
// calldata (duplicate) but memory != storage (distinct). The fix adds
// `paramStorageRefs` (== `location == storage`, per param) to the comparison.
//
// A MEMORY argument binds the memory overload unambiguously (a memory array
// cannot convert to a storage parameter), so `callMemory` dispatches to it and
// returns `length + 100`. NOTE: a STORAGE argument is AMBIGUOUS between the two
// overloads (a storage array binds the storage param exactly AND converts to the
// memory param), which solc REJECTS — pinned by the invalid fixture below.
contract OverloadMemVsStorageHarness {
    function f(uint256[] memory x) internal pure returns (uint256) {
        return x.length + 100;
    }

    function f(uint256[] storage x) internal view returns (uint256) {
        // Reachable only if selected; the storage overload must legally coexist.
        return x.length + 200;
    }

    // Memory argument -> memory overload: 3 + 100 = 103.
    function callMemory() external pure returns (uint256) {
        uint256[] memory m = new uint256[](3);
        return f(m);
    }
}
