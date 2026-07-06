// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract TypedFallbackNoReturn {
    fallback(bytes calldata input) external {
        input;
    }
}
