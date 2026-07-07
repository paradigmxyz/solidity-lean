// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {TupleHoles} from "../src/TupleHoles.sol";

/// Ground truth (pinned solc 0.8.35 / Foundry EVM) for tuple-with-hole
/// assignment: held-out components are not bound, but their RHS computation
/// still runs, and the canonical value-carrying call idiom debits the caller.
contract TupleHolesForgeTest {
    receive() external payable {}

    function testAssignTrailingHole() public {
        TupleHoles t = new TupleHoles();
        require(t.assignTrailingHole() == 71, "trailing");
    }

    function testAssignLeadingHole() public {
        TupleHoles t = new TupleHoles();
        require(t.assignLeadingHole() == 91, "leading");
    }

    function testDeclMiddleHole() public {
        TupleHoles t = new TupleHoles();
        require(t.declMiddleHole() == 351, "middle");
    }

    /// `(bool ok, ) = target.call{value: 1}("")`: the send debits the caller
    /// (funded with 10) to 9; the returned `bytes` are held out.
    function testCallTrailingHoleDebits() public {
        TupleHoles t = new TupleHoles{value: 10}();
        require(t.callTrailingHole(address(this)) == 9, "debit");
    }
}
