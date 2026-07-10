// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Pinned solc 0.8.35 REJECTS a NON-UTF-8 hex-string literal as a string.concat
// argument (Error 9977 "Invalid type for argument in the string.concat function
// call. string type is required"), because 0xff is not valid UTF-8 and so the
// StringLiteralType is not implicitly convertible to `string memory`.
contract Bad {
    function bad() external pure returns (string memory) {
        return string.concat(hex"ff");
    }
}
