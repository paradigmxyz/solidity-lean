// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A plain (non-`unicode`, non-`hex"..."`) double-quoted string literal whose
// bytes are NOT valid UTF-8: `"\xff\x00\x41"` == the three bytes 0xFF 0x00 0x41.
// solc gives such a literal the type `literal_string hex"ff0041"` - the SAME
// type as a `hex"..."` literal - so it converts to `bytes` (accepted) but NOT
// to `string` (rejected; see invalid/StringNonUtf8.sol). In solc's AST the
// literal has `kind:"string"`, a `hexValue:"ff0041"`, and NO `value` field
// (solc omits `value` when the bytes aren't valid UTF-8). The importer used to
// die on the missing `value`; it now falls back to `hexValue` and lowers the
// literal exactly like a `hex"..."` literal.
contract NonUtf8StringLiteral {
    // `bytes(...)` explicit-conversion context.
    function convLength() external pure returns (uint256) {
        return bytes("\xff\x00\x41").length;
    }

    function convByteAt(uint256 index) external pure returns (uint256) {
        return uint256(uint8(bytes("\xff\x00\x41")[index]));
    }

    function convHash() external pure returns (bytes32) {
        return keccak256(bytes("\xff\x00\x41"));
    }

    // Direct assignment to a `bytes memory` local (implicit-conversion context).
    function assignByteAt(uint256 index) external pure returns (uint256) {
        bytes memory b = "\xff\x00\x41";
        return uint256(uint8(b[index]));
    }
}
