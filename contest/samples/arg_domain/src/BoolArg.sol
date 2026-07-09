// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Regression guard: an out-of-domain scalar arg is not a legal high-level call.
// entry.args = [{"word": 5}] for a bool param: the EVM decoder reverts on a dirty
// bool while Solidus rejects/accepts, fabricating a divergence. Must be
// REJECT_MALFORMED, never a qualifying gap.
contract BoolArg {
    function f(bool x) external pure returns (uint256) { return x ? 1 : 0; }
}
