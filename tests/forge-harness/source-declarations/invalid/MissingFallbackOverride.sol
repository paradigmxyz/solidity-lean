// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MissingFallbackOverrideBase {
    fallback() external virtual {}
}

contract MissingFallbackOverride is MissingFallbackOverrideBase {
    fallback() external {}
}
