// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {OverrejectCallposBatchHarnessTarget} from "../src/OverrejectCallposBatch.sol";

contract OverrejectCallposBatchForgeTest {
    OverrejectCallposBatchHarnessTarget private target =
        new OverrejectCallposBatchHarnessTarget();

    // A — `uint x = outer(inner())` composed value.
    function testComposeVal() public {
        require(target.composeVal() == 103, "outer(inner()) must equal 103");
    }

    // A — eval-order: inner() before outer() (order trail = 12).
    function testOrderCompose() public {
        require(target.orderCompose() == 12, "inner then outer order must be 12");
    }

    // B — varDecl index read `uint x = mp[f()]`.
    function testReadIdx() public {
        require(target.readIdx() == 55, "mp[f()] read must equal 55");
    }

    // B — plain-assign index read `y = mp[f()]`.
    function testAssignIdx() public {
        require(target.assignIdx() == 66, "y = mp[f()] must equal 66");
    }

    // B — index read in a binary operand `mp[f()] + 1`.
    function testBinIdx() public {
        require(target.binIdx() == 56, "mp[f()] + 1 must equal 56");
    }

    // E — index-assign with call RHS `mp[f()] = gval()`.
    function testWriteIdx() public {
        require(target.writeIdx() == 77, "mp[f()] = gval() must store 77");
    }

    // E — eval-order: gval() (RHS) before f() (index) (order trail = 21).
    function testWriteIdxOrder() public {
        require(target.writeIdxOrder() == 21, "RHS then index order must be 21");
    }

    // Controls — call-free paths unchanged.
    function testPlainVarDeclControl() public {
        require(target.plainVarDeclControl() == 5, "plain varDecl must equal 5");
    }

    function testPlainIdxControl() public {
        require(target.plainIdxControl() == 9, "plain index read must equal 9");
    }

    function testPlainWriteControl() public {
        require(target.plainWriteControl() == 88, "plain index assign must equal 88");
    }
}
