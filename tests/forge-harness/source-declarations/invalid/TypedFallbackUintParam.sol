// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract TypedFallbackUintParam {
    fallback(uint256 input) external returns (bytes memory) {
        input;
        return "";
    }
}
