// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// solc REJECTS: `unicode"😀"` is 4 UTF-8 bytes (0xF0 0x9F 0x98 0x80), which is
// larger than `bytes2`. Diagnostic: "Literal is larger than the type."
// This guards against the interpreter over-accepting the conversion (which it
// did while the importer mis-decoded the emoji to two null bytes, making it
// spuriously fit bytes2 as 0x0000).
contract Bytes2NonBmp {
    function f() external pure returns (bytes2) {
        return bytes2(unicode"😀");
    }
}
