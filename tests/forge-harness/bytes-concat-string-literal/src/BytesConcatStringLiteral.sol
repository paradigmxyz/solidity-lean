// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// SB1 accept-path pin. solc's `bytes.concat` accepts a string *literal*
// (StringLiteralType is implicitly convertible to both `bytes32` and
// `bytes memory`) alongside `bytesN` values, but rejects `string`-typed
// *values* (see ../invalid/BytesConcatStringVar.sol). SolidCore's fix keeps
// this literal/value distinction, so the accept path stays correct.
contract BytesConcatStringLiteral {
    function joinLiteral() external pure returns (bytes memory) {
        return bytes.concat("abc", bytes4(0x01020304));
    }

    function joinUnicode() external pure returns (bytes memory) {
        return bytes.concat(unicode"é");
    }
}
