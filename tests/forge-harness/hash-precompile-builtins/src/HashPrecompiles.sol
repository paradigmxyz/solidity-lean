// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Harness exercising the sha256 (precompile 0x02) and ripemd160 (precompile
// 0x03) builtins. Each function passes an explicit `bytes memory` payload to the
// builtin so the calldata the interpreter forms for the STATICCALL is exactly
// the payload bytes, matching the EVM precompile ABI (raw input, no length
// prefix). `ripemd160` returns `bytes20` (left-aligned in a 32-byte word on the
// EVM); `ripemd160Word` exposes the numeric (right-aligned) digest so the
// value-level Lean comparison is unambiguous.
contract HashPrecompilesHarnessTarget {
    function sha256Of(bytes memory data) external pure returns (bytes32) {
        return sha256(data);
    }

    function ripemd160Of(bytes memory data) external pure returns (bytes20) {
        return ripemd160(data);
    }

    function ripemd160Word(bytes memory data) external pure returns (uint256) {
        return uint256(uint160(ripemd160(data)));
    }
}
