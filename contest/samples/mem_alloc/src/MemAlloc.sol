// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Regression guard for the X-EXTCALL fix: `new uint256[](n)` / `new bytes(n)`
// are in-memory allocations, NOT contract creations, and must NOT be excluded.
// The function returns a scalar, so it is faithfully comparable.
contract MemAlloc {
    function sum(uint256 n) external pure returns (uint256) {
        uint256[] memory a = new uint256[](n);
        bytes memory b = new bytes(n);      // also a NewExpression, not external
        uint256 s = b.length;
        for (uint256 i = 0; i < n; i++) { a[i] = i + 1; s += a[i]; }
        return s;                            // n + sum(1..n)
    }
}
