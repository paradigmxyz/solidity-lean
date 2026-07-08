// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Fixed-point value type whose bound operator bodies DIFFER from the built-in
// operators on the underlying int256 word. `fixedMul` rescales by 1e18, so a
// correct dispatch must run the operator function, not the built-in `*` on the
// raw words. This is the wrong-value soundness case (finding G1): under the bug
// `500e18 + 500e18 * 0.1` evaluated the built-in `*` (no /1e18 rescale) and
// produced ~5e37; correct dispatch produces 550e18.
type Fixed is int256;

function fixedAdd(Fixed a, Fixed b) pure returns (Fixed) {
    return Fixed.wrap(Fixed.unwrap(a) + Fixed.unwrap(b));
}

function fixedSub(Fixed a, Fixed b) pure returns (Fixed) {
    return Fixed.wrap(Fixed.unwrap(a) - Fixed.unwrap(b));
}

function fixedMul(Fixed a, Fixed b) pure returns (Fixed) {
    int256 scale = 1e18;
    return Fixed.wrap((Fixed.unwrap(a) * Fixed.unwrap(b)) / scale);
}

function fixedNeg(Fixed a) pure returns (Fixed) {
    return Fixed.wrap(-Fixed.unwrap(a));
}

function fixedLt(Fixed a, Fixed b) pure returns (bool) {
    return Fixed.unwrap(a) < Fixed.unwrap(b);
}

function fixedEq(Fixed a, Fixed b) pure returns (bool) {
    return Fixed.unwrap(a) == Fixed.unwrap(b);
}

using {
    fixedAdd as +,
    fixedSub as -,
    fixedMul as *,
    fixedNeg as -,
    fixedLt as <,
    fixedEq as ==
} for Fixed global;

// uint256 type whose operator body is CHECKED (no `unchecked` block). The
// operator function runs with its own context, so `+` panics 0x11 on overflow
// even when the call site is inside an `unchecked` block.
type CheckedWord is uint256;

function checkedWordAdd(CheckedWord a, CheckedWord b) pure returns (CheckedWord) {
    return CheckedWord.wrap(CheckedWord.unwrap(a) + CheckedWord.unwrap(b));
}

using {checkedWordAdd as +} for CheckedWord global;

// uint256 type whose operator body is UNCHECKED; the operator function wraps
// modulo 2^256 even when the call site is a checked context.
type WrappingWord is uint256;

function wrappingWordAdd(WrappingWord a, WrappingWord b)
    pure
    returns (WrappingWord)
{
    unchecked {
        return WrappingWord.wrap(WrappingWord.unwrap(a) + WrappingWord.unwrap(b));
    }
}

using {wrappingWordAdd as +} for WrappingWord global;

contract UdvtOperatorDispatch {
    // `value + value * percentage`, all fixed-point (1e18 scaling). Under the
    // G1 bug `*` used the built-in int256 multiply (no /1e18 rescale) yielding a
    // wildly wrong value; correct dispatch runs `fixedMul` → 550e18.
    function applyInterest(int256 value, int256 percentage)
        public
        pure
        returns (int256)
    {
        Fixed v = Fixed.wrap(value);
        Fixed p = Fixed.wrap(percentage);
        return Fixed.unwrap(v + v * p);
    }

    // Unary minus dispatched to `fixedNeg`, applied twice → identity.
    function doubleNeg(int256 value) public pure returns (int256) {
        Fixed a = Fixed.wrap(value);
        return Fixed.unwrap(-(-a));
    }

    // Binary minus dispatched to `fixedSub`, disambiguated from unary `fixedNeg`.
    function diff(int256 a, int256 b) public pure returns (int256) {
        return Fixed.unwrap(Fixed.wrap(a) - Fixed.wrap(b));
    }

    // Comparison operators return `bool` via `fixedLt` / `fixedEq`.
    function less(int256 a, int256 b) public pure returns (bool) {
        return Fixed.wrap(a) < Fixed.wrap(b);
    }

    function equal(int256 a, int256 b) public pure returns (bool) {
        return Fixed.wrap(a) == Fixed.wrap(b);
    }

    // Operator body is checked: even though the call site is inside an
    // `unchecked` block, the add panics 0x11 when `x + 1` overflows 2^256.
    function checkedOpOverflow(uint256 x) public pure returns (uint256) {
        unchecked {
            return CheckedWord.unwrap(CheckedWord.wrap(x) + CheckedWord.wrap(1));
        }
    }

    // Operator body is unchecked: even from a checked call site the add wraps
    // modulo 2^256 (max + 1 == 0).
    function uncheckedOpWraps(uint256 x) public pure returns (uint256) {
        return WrappingWord.unwrap(WrappingWord.wrap(x) + WrappingWord.wrap(1));
    }
}
