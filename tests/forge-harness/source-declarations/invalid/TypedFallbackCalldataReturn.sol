// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract TypedFallbackCalldataReturn {
    fallback(bytes calldata input) external returns (bytes calldata) {
        return input;
    }
}
