// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MultipleFallback {
    fallback() external {}

    fallback(bytes calldata input) external returns (bytes memory) {
        return input;
    }
}
