// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract PayableFallbackOverrideBase {
    fallback() external virtual {}
}

contract PayableFallbackOverride is PayableFallbackOverrideBase {
    fallback() external payable override {}
}
