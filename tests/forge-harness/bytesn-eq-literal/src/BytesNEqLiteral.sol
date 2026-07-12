// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// #180: `==`/`!=` between a `bytesN` value and a BARE string/hex literal. solc
// 0.8.35 implicitly converts the literal to the bytesN operand's value type and
// compares as value types (no explicit cast needed). The model over-rejected at
// typecheck because it checked the raw dynamic `bytes`/`string` literal type for
// equality-comparability instead of the common (converted) bytesN value type.
contract BytesNEqLiteral {
    // "abcd" -> bytes4 0x61626364
    function a(bytes4 x) external pure returns (bool) { return x == "abcd"; }
    // hex"1234" -> bytes4 0x12340000
    function b(bytes4 x) external pure returns (bool) { return x != hex"1234"; }
    // hex"00" -> bytes32 0x00..00 = 0
    function c(bytes32 x) external pure returns (bool) { return x == hex"00"; }
}
