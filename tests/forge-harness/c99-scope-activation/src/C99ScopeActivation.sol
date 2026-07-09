// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// G21 pin (docs/solidity-lean-solc-deep-comparison.md): Solidity uses C99 block
// scoping — a local declaration is in scope only AFTER its declaration point,
// NOT hoisted to the top of its block. Each probe's value distinguishes C99
// activation from whole-block (JS `var`-style) hoisting.
contract C99ScopeActivationHarnessTarget {
    // Before the inner `x` is declared, `x` still resolves to the OUTER x (=1).
    // C99: y = 1, then inner x = 100 -> 1*1000 + 100 = 1100.
    // Hoisting would make `uint y = x` read an uninitialized inner x (=0) -> 100.
    function blockActivation() public pure returns (uint256) {
        uint256 x = 1;
        {
            uint256 y = x;
            uint256 x = 100;
            return y * 1000 + x;
        }
    }

    // The initializer of the inner `x` sees the OUTER x (=5), because the inner
    // `x` is not yet activated at its own initializer. C99: inner x = 5 + 1 = 6.
    // Hoisting would read an uninitialized inner x (=0) -> 1.
    function selfInitFromOuter() public pure returns (uint256) {
        uint256 x = 5;
        {
            uint256 x = x + 1;
            return x;
        }
    }
}
