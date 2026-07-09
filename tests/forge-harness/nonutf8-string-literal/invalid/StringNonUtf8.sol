// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// solc REJECTS: a plain string literal whose bytes are not valid UTF-8
// (`"\xff\x00\x41"`) has type `literal_string hex"ff0041"`, which is NOT
// implicitly convertible to `string`. Diagnostic:
//   "Type literal_string hex\"ff0041\" is not implicitly convertible to
//    expected type string memory. Contains invalid UTF-8 sequence at position 0."
// The importer lowers such a literal as a `hex"..."` literal (Lean type
// Ty.bytes), so the Lean checker likewise rejects assigning it to `string`,
// matching solc's accept(bytes)/reject(string) boundary.
contract StringNonUtf8 {
    function f() external pure returns (string memory) {
        string memory s = "\xff\x00\x41";
        return s;
    }
}
