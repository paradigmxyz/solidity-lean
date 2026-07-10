// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// STRINGCONCAT-HEXLIT-UTF8 (divergence #152): pinned solc 0.8.35 accepts a
// hex-string literal (`hex"..."`) as a `string.concat` argument exactly when its
// bytes are valid UTF-8 (StringLiteralType is implicitly convertible to
// `string memory` iff `util::validateUTF8` passes). Each function below is
// accepted by solc and returns the concatenated string.
contract StringConcatHexLit {
    // hex"61" == byte 0x61 == "a".
    function joinHex() external pure returns (string memory) {
        return string.concat(hex"61");
    }

    // "a" ++ hex"62" == "ab".
    function joinMixed() external pure returns (string memory) {
        return string.concat("a", hex"62");
    }

    // "x" ++ hex"79" == "xy".
    function joinXy() external pure returns (string memory) {
        return string.concat("x", hex"79");
    }

    // hex"e298ba" is the 3-byte UTF-8 encoding of U+263A (☺).
    function joinMultibyte() external pure returns (string memory) {
        return string.concat(hex"e298ba");
    }
}
