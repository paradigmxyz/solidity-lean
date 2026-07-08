// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// G15 — a conditional of two number literals carries the ternary's COMMON
// (mobile) type, not `uint256` and not the then-branch's width. solc
// `TypeChecker::visit(Conditional)` sets the type to
// `commonType(trueExpr->mobileType(), falseExpr->mobileType())`, so
// `(t ? 63 : 255)` is `uint8`. The width is observable when the result feeds
// checked arithmetic that overflows at that width.
contract TernaryLiteralMobileTypeHarnessTarget {
    // `uint8` mobile type: assignable to a `uint8` local (Solidus formerly
    // over-rejected this, typing the ternary `uint256`).
    function narrowAssign(bool t) external pure returns (uint8) {
        uint8 r = t ? 63 : 255;
        return r;
    }

    // The `uint8` conditional widens implicitly to `uint256`.
    function widenAssign(bool t) external pure returns (uint256) {
        uint256 r = t ? 63 : 255;
        return r;
    }

    // The `+ 1` runs in `uint8` (the ternary's mobile type), so `255 + 1`
    // overflows and panics 0x11 in checked mode even though nothing here is
    // wider than `uint8`.
    function widthPanic(bool t) external pure returns (uint8) {
        uint8 r = (t ? 63 : 255) + 1;
        return r;
    }

    // Larger literals push the mobile common type up to `uint16`.
    function uint16Common(bool t) external pure returns (uint16) {
        uint16 r = t ? 300 : 400;
        return r;
    }
}
