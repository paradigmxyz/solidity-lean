// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// BYTESN-IDENT-INDEX (#175 local/param, #176 state var): indexing a `bytesN`
// value by a BARE IDENTIFIER base. `a[i]` where `a` is a `bytesN` local,
// parameter, or state variable extracts the i-th byte (solc returns `bytes1`),
// and on an out-of-range index (i >= N) Panics 0x32 (array out-of-bounds).
// solidity-lean's env-free `Expr.toCore?` ident-index arm could not see the
// identifier's declared type, so it emitted a generic `index`/`storageIndex`
// that reverted Panic 0x00 (type mismatch) for every in-range index — and, for
// state vars, Panic 0x00 (instead of 0x32) out of range. The fix, in the
// type-directed `resolveStructs` pre-pass, rewrites `name[i]` for a bytesN
// identifier to `bytesN(name)[i]`, routing it to the correct fixed-bytes path.
contract BytesNIdentIndexHarnessTarget {
    bytes32 public b;
    bytes4 public b4;

    function setB(bytes32 v) external { b = v; }
    function setB4(bytes4 v) external { b4 = v; }

    // #175 PARAM: bytes32 / bytes4 parameter indexed by a bare `i`.
    function fParam(bytes32 a, uint256 i) external pure returns (bytes1) { return a[i]; }
    function fParam4(bytes4 a, uint256 i) external pure returns (bytes1) { return a[i]; }

    // #175 LOCAL: bytes32 local indexed by a bare `i`.
    function fLocal(uint256 i) external pure returns (bytes1) {
        bytes32 a = 0x00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff;
        return a[i];
    }

    // #176 STATE VAR: bytes32 / bytes4 state variable indexed by a bare `i`.
    function getByte(uint256 i) external view returns (bytes1) { return b[i]; }
    function getByte4(uint256 i) external view returns (bytes1) { return b4[i]; }
}
