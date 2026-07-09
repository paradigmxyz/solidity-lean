// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

// #54 (MOD-RET): a `return` carrying ANY expression inside a MODIFIER body is
// rejected by solc 0.8.35 (TypeError 7552 "Return arguments not allowed",
// TypeChecker::endVisit(Return), TypeChecker.cpp:1133-1146 — a modifier's
// functionReturnParameters is nullptr). The `_;` placeholder is present so the
// return-argument error is the salient divergence (not a missing-placeholder
// error). Even a VOID-typed argument like `delete x` is rejected.
contract ModifierReturnDelete {
    uint256 x;
    modifier m() {
        return delete x;
        _;
    }
    function f() public m {}
}
