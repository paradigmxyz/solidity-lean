// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Stage-C pin for the boundary-completion arc
// (docs/refs-completion-solc-research.md §2): internal function pointers are
// small sequential dispatch IDs — storable 8-byte state variables, passable
// as arguments and returns, callable through data-dependent values; calling
// an uninitialized pointer panics 0x51; recursion through a pointer works.
// Every probe is self-contained (fresh state).
contract InternalFnPointersHarnessTarget {
    function(uint256) internal pure returns (uint256) fp;

    function dbl(uint256 x) internal pure returns (uint256) {
        return 2 * x;
    }

    function trip(uint256 x) internal pure returns (uint256) {
        return 3 * x;
    }

    // Storage round-trip: write a data-dependent pointer to an 8-byte state
    // variable, read it back, dispatch. true -> dbl(21)=42, false -> 63.
    function viaStorage(bool b, uint256 x) public returns (uint256) {
        fp = b ? dbl : trip;
        return fp(x);
    }

    function applyTwice(
        function(uint256) internal pure returns (uint256) f,
        uint256 x
    ) internal pure returns (uint256) {
        return f(f(x));
    }

    // Pointer as an ARGUMENT to an internal function: dbl(dbl(3)) = 12.
    function viaParam(uint256 x) public pure returns (uint256) {
        return applyTwice(dbl, x);
    }

    function pick(bool b)
        internal
        pure
        returns (function(uint256) internal pure returns (uint256))
    {
        return b ? dbl : trip;
    }

    // Pointer as a RETURN of an internal function: pick(false)(10) = 30.
    function viaReturn(bool b, uint256 x) public pure returns (uint256) {
        function(uint256) internal pure returns (uint256) g = pick(b);
        return g(x);
    }

    // Calling an uninitialized pointer panics 0x51 (x <= 10 leaves g unset).
    function callUninitialized(uint256 x) public pure returns (uint256) {
        function(uint256) internal pure returns (uint256) g;
        if (x > 10) {
            g = dbl;
        }
        return g(x);
    }

    function countdown(uint256 n) internal pure returns (uint256) {
        if (n == 0) {
            return 0;
        }
        // Data-dependent pointer (defeats static aliasing) — the recursive
        // call goes through the runtime dispatch ID.
        function(uint256) internal pure returns (uint256) self =
            n % 2 == 0 ? countdown : countdown;
        return self(n - 1) + 1;
    }

    // Recursion THROUGH a pointer: countdown(7) = 7.
    function viaRecursion(uint256 n) public pure returns (uint256) {
        return countdown(n);
    }
}
