// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// EXTERNAL fn-type conversion under solc's calldata->memory normalization:
// `this.f` for `f(uint256[] calldata)` has type
// `function (uint256[] memory) external`, so assigning it to a declared
// `function(uint256[] memory) external` fn-type variable is ACCEPTED (the
// model formerly over-rejected with expectedType). The pointers are CALLED
// through, pinning that the accepted conversions also run correctly on the
// real EVM. A calldata-RETURNING external fn normalizes the same way
// (`callThroughCalldataRetPtr`); its model-side EXECUTION hits a pre-existing
// self-dispatch gap for `returns (uint256[] calldata)` (reproducible with a
// direct `this.fRet(xs)` call, no function pointer involved), so the Lean
// side pins acceptance + the memory-return pointer execution, and Forge pins
// the full EVM behaviour of all three.
contract ExtfnLocationErasureHarnessTarget {
    function f(uint256[] calldata a) external pure returns (uint256) {
        return a.length + a[0];
    }

    function fRet(uint256[] calldata a) external pure returns (uint256[] calldata) {
        return a;
    }

    function fRetMem(uint256[] calldata a) external pure returns (uint256[] memory) {
        return a;
    }

    // Assign this.f (calldata param) to a memory-located declared fn type,
    // then call through the pointer.
    function callThroughPtr(uint256 seed) external view returns (uint256) {
        function(uint256[] memory) external pure returns (uint256) h = this.f;
        uint256[] memory xs = new uint256[](3);
        xs[0] = seed;
        return h(xs);
    }

    // Memory-array-returning external fn (calldata param) assigned to a
    // memory/memory declared type, called through the pointer.
    function callThroughRetPtr(uint256 seed) external view returns (uint256) {
        function(uint256[] memory) external pure returns (uint256[] memory) h = this.fRetMem;
        uint256[] memory xs = new uint256[](2);
        xs[1] = seed;
        uint256[] memory ys = h(xs);
        return ys[1] + ys.length;
    }

    // Calldata-RETURNING external fn assigned to a memory-return declared
    // type (the return-location normalization shape), called through the
    // pointer. Runs on both engines (see header).
    function callThroughCalldataRetPtr(uint256 seed) external view returns (uint256) {
        function(uint256[] memory) external pure returns (uint256[] memory) h = this.fRet;
        uint256[] memory xs = new uint256[](2);
        xs[1] = seed;
        uint256[] memory ys = h(xs);
        return ys[1] + ys.length;
    }

    // Direct self-call of the calldata-array-RETURNING external fn (no
    // function pointer): the minimal repro of the former self-dispatch
    // return-path gap. The callee's `uint256[] calldata` return is
    // memory-localized at entry, so the re-encode returns the array.
    function callDirectCalldataRet(uint256 seed) external view returns (uint256) {
        uint256[] memory xs = new uint256[](2);
        xs[1] = seed;
        uint256[] memory ys = this.fRet(xs);
        return ys[1] + ys.length;
    }
}
