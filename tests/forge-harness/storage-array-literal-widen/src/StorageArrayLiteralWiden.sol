// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Storage inline-array-literal element-widening boundary. Unlike a MEMORY array
// (`uint256[2] memory x = [50,0]` — the classic uint8[2] ↛ uint256[2] gotcha,
// which solc REJECTS), a NON-POINTER STORAGE array — a state variable — runs
// solc's storage-copy conversion branch, so each element only needs to be
// IMPLICITLY CONVERTIBLE to the target element type. Pinned solc 0.8.35 ACCEPTS
// every state-variable initializer below and compiles it; each getter reads the
// stored elements back into a scalar so both Forge and the Lean interpreter can
// pin the runtime values. The model previously OVER-REJECTED these (fail-closed
// `expectedType(u256[2])(u256[2])`).
contract StorageArrayLiteralWidenHarnessTarget {
    // The submitted divergence: uint8[2] literal → uint256[2] storage.
    uint256[2] public arr = [50, 0];
    // uint8[3] literal → uint16[3] storage widen.
    uint16[3] private wide16 = [1, 2, 3];
    // nested uint8[2][2] literal → uint256[2][2] storage widen.
    uint256[2][2] private nested = [[1, 2], [3, 4]];
    // typed leading element still widens for storage: uint8 → uint256.
    uint256[2] private typedLead = [uint8(9), 7];

    // The exact submission entry.
    function run() external view returns (uint256, uint256) {
        return (arr[0], arr[1]);
    }

    // Single-word getters (interpreter word-pins).
    function a0() external view returns (uint256) {
        return arr[0]; // 50
    }

    function a1() external view returns (uint256) {
        return arr[1]; // 0
    }

    function wide16Sum() external view returns (uint256) {
        return uint256(wide16[0]) * 10000 + uint256(wide16[1]) * 100
            + uint256(wide16[2]); // 10203
    }

    function nestedSum() external view returns (uint256) {
        return nested[0][0] * 1000 + nested[0][1] * 100
            + nested[1][0] * 10 + nested[1][1]; // 1234
    }

    function typedLeadSum() external view returns (uint256) {
        return typedLead[0] * 1000 + typedLead[1]; // 9007
    }
}
