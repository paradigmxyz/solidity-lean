// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

/// Tuple-with-hole assignment: solc allows omitted (skipped) components in a
/// tuple assignment / declaration LHS (`(a, ) = …`, `(, b) = …`, `(a, , c) = …`).
/// Only the *binding* of a held-out component is skipped; the corresponding RHS
/// component is still evaluated in full (its side effects happen). The canonical
/// idiom is `(bool ok, ) = target.call{value: v}("")`, which discards the
/// returned `bytes` while the value-carrying call still debits the caller.
///
/// The held-out slots use a storage post-increment (`pokes++`) so that a bump of
/// `pokes` is observable iff that RHS component was evaluated.
contract TupleHoles {
    uint256 public pokes;

    constructor() payable {}

    /// Trailing hole in an assignment LHS: `pokes++` (held out) still runs.
    function assignTrailingHole() external returns (uint256) {
        uint256 a;
        (a, ) = (7, pokes++);
        return a * 10 + pokes; // 7*10 + 1 = 71
    }

    /// Leading hole in an assignment LHS: `pokes++` (held out) still runs.
    function assignLeadingHole() external returns (uint256) {
        uint256 b;
        ( , b) = (pokes++, 9);
        return b * 10 + pokes; // 9*10 + 1 = 91
    }

    /// Middle hole in a declaration LHS with a side-effecting held-out slot.
    function declMiddleHole() external returns (uint256) {
        (uint256 l, , uint256 r) = (3, pokes++, 5);
        return l * 100 + r * 10 + pokes; // 3*100 + 5*10 + 1 = 351
    }

    /// Canonical idiom: hole out the returned `bytes` of a value-carrying call.
    /// A successful send debits the caller; the observed self balance reflects it.
    function callTrailingHole(address target) external returns (uint256) {
        (bool ok, ) = target.call{value: 1}("");
        require(ok, "call failed");
        return address(this).balance;
    }
}
