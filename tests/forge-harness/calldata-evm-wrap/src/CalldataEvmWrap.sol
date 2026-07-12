// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// WS3 / #129 CALLDATA-TAIL-WRAP.
//
// When a CALLDATA aggregate of DYNAMIC elements is accessed element-by-element,
// solc follows the element's tail pointer with `access_calldata_tail`
// (YulUtilFunctions.cpp): the offset is validated with a SIGNED `slt` (so a
// high-bit / "negative" offset PASSES) and `addr := add(base_ref, rel_offset)`
// is computed MOD 2^256 and WRAPS. A crafted high-bit tail offset therefore
// wraps to an in-bounds region and the access SUCCEEDS with real bytes, where a
// bounds-then-reject decoder would over-revert.
//
// Contrast: a TOP-LEVEL dynamic param offset is validated UNSIGNED
// (`gt(offset, 0xffffffffffffffff)` in tupleDecoder) and CANNOT wrap. The
// malformed-calldata revert matrix (eager/memory path) is preserved.
contract CalldataEvmWrapTarget {
    // Access a[0] of a calldata bytes[] -> routes through access_calldata_tail.
    function firstElem(bytes[] calldata a) external pure returns (bytes memory) {
        return a[0];
    }

    // Length only -> never follows a tail pointer (control).
    function len(bytes[] calldata a) external pure returns (uint256) {
        return a.length;
    }
}
