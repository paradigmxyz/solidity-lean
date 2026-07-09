// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// A scalar-only custom error: both params are statically-encoded words, so the
// revert compares faithfully in the `custom:<Name>:...` normal form on both
// engines (no X-RETABI fence). End-to-end proof of the scalar custom-error
// revert comparison path (audit round 3 fixed complex params to REJECTED_OOS
// but left the scalar path only unit-tested).
error Bad(uint256 code, bool flag);

contract Reverter {
    function f() external pure {
        revert Bad(42, true);
    }
}
