// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Harness-hardening probe: the Error(string) revert reason is concatenated RAW
// (not hex-encoded) into the normal form on BOTH engines (observable.py:375 /
// Lean "error:" ++ s). This reason embeds every structural token the comparator
// uses -- the "|" delimiter, the ##EVT## / ##STO## section markers, and fake
// outcome tokens (revert|panic:99, success|w:5). If solidity-lean and solc+EVM
// render this identically -> NO_DIVERGENCE (raw concat is symmetric/safe). A
// mismatch would be a marker-injection desync = fabricated wrong-revert gap.
contract Injector {
    function f() external pure returns (uint256) {
        require(false, "a|b##EVT##c##STO##d revert|panic:99 success|w:5 revert|custom:X:1");
        return 0;
    }
}
