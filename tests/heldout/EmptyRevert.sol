// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Held-out: an empty revert (no data) next to a bounded loop. The certificate must tell the
/// empty revert (status revert, empty output, at any gas above the bound) from running out of
/// gas (exceptional halt, all gas used): the expected theorem's allowed statuses separate them.
/// The replay case oog-as-revert lowers the recorded gas bound and must be refused.
contract EmptyRevert {
    uint256 public acc;

    /// @custom:requires n <= 64
    /// @custom:ensures acc == old(acc) + n
    function spin(uint256 n) external {
        if (n == 0) revert();
        uint256 a = acc;
        /// @custom:invariant i <= n
        /// @custom:invariant a == old(acc) + i
        /// @custom:decreases n - i
        for (uint256 i = 0; i < n; i++) {
            a = a + 1;
        }
        acc = a;
    }
}
