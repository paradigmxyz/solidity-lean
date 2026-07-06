// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract TypedFallbackMemoryParam {
    fallback(bytes memory input) external returns (bytes memory) {
        return input;
    }
}
