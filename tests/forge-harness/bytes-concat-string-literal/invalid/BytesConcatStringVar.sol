// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// solc rejects a `string`-typed *value* in bytes.concat (Error 8015: bytes or
// fixed bytes type is required, but string memory provided). SB1 reject pin.
contract Bad {
    function bad(string memory s) external pure returns (bytes memory) {
        return bytes.concat(s);
    }
}
