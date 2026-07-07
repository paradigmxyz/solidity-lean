// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {TupleLiteralHoistHarnessTarget} from "../src/TupleLiteralHoist.sol";

// Forge ground truth for the stage-B tuple-literal hoisting pin. A fresh
// instance per probe keeps the order log independent.
contract TupleLiteralHoistForgeTest {
    function testAssignPair() public {
        TupleLiteralHoistHarnessTarget target =
            new TupleLiteralHoistHarnessTarget();
        require(target.assignPair() == 11022012, "assignPair");
    }

    function testAssignHole() public {
        TupleLiteralHoistHarnessTarget target =
            new TupleLiteralHoistHarnessTarget();
        require(target.assignHole() == 22012, "assignHole");
    }

    function testDeclPair() public {
        TupleLiteralHoistHarnessTarget target =
            new TupleLiteralHoistHarnessTarget();
        require(target.declPair() == 22011021, "declPair");
    }
}
