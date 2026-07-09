// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// The explicitly-typed uint8(1) is fine, but the trailing bare number literal
// `2` is still rejected: packed encoding cannot pack a literal. solc: "Cannot
// perform packed encoding for a literal. Please convert it to an explicit type
// first."
contract C {
    function f() external pure returns (bytes memory) {
        return abi.encodePacked(uint8(1), 2);
    }
}
