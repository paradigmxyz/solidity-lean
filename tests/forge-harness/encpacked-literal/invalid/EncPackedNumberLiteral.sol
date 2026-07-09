// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A bare number literal has no packed byte width. solc rejects it in packed
// mode: "Cannot perform packed encoding for a literal. Please convert it to an
// explicit type first."
contract C {
    function f() external pure returns (bytes memory) {
        return abi.encodePacked(1);
    }
}
