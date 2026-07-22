// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// ABI-DECODE-TOTAL-HEAD-SIZE lane: solc's `abi.decode` opens with
// `if slt(sub(dataEnd, headStart), <totalHeadSize>) { revert(0,0) }` — the
// WHOLE static head of the decoded tuple must be present BEFORE any component
// decode. Short data therefore reverts EMPTY upfront; it never follows a
// garbage offset into an oversized array length (which would Panic 0x41).
// The nested dynamic-struct decoder (`abi_decode_t_struct`) emits its own
// `slt(sub(end, offset), <headSize>)` with the same empty revert.
contract AbiDecodeShortHeadHarnessTarget {
    struct ShortHeadPair {
        uint256[] a;
        uint256 b;
    }

    // Adjudicated repro: 63 bytes of data for a `(uint256[], uint256)` head of
    // 64 (`abi.encodePacked(uint256(31), uint248(1))`) -> EMPTY revert (real
    // EVM), NOT Panic(0x41) from following offset 31 into a huge length.
    function decodeShort() external pure returns (uint256) {
        bytes memory data = abi.encodePacked(uint256(31), uint248(1));
        (uint256[] memory a, uint256 b) =
            abi.decode(data, (uint256[], uint256));
        return a.length + b;
    }

    // Control: a well-formed encoding still decodes.
    function decodeControl() external pure returns (uint256, uint256) {
        uint256[] memory arr = new uint256[](2);
        arr[0] = 7;
        arr[1] = 9;
        bytes memory data = abi.encode(arr, uint256(5));
        (uint256[] memory a, uint256 b) =
            abi.decode(data, (uint256[], uint256));
        return (a[0] + a[1], b);
    }

    // Nested-tuple short head: outer offset 32 points at a struct whose
    // 64-byte member head is truncated to 63 bytes -> EMPTY revert at the
    // struct-frame head check (NOT Panic(0x41) from the member offset 31
    // resolving to an oversized length).
    function decodeNestedShort() external pure returns (uint256) {
        bytes memory data =
            abi.encodePacked(uint256(32), uint256(31), uint248(1));
        ShortHeadPair memory p = abi.decode(data, (ShortHeadPair));
        return p.a.length + p.b;
    }
}
