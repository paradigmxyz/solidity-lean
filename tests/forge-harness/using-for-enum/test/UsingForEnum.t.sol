// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {UsingForEnumHarnessTarget} from "../src/UsingForEnum.sol";

// Forge ground truth for EU1: member-call dispatch over an enum receiver bound
// via `using {f} for E` (file-level global, contract-level brace, attached
// library). solc lowers `c.f(args)` to `f(c, args)`.
contract UsingForEnumForgeTest {
    function newTarget() internal returns (UsingForEnumHarnessTarget) {
        return new UsingForEnumHarnessTarget();
    }

    // Color(2) = Blue; rank(Blue) = 2 + 1 = 3.
    function testViaRank() public {
        require(newTarget().viaRank(2) == 3, "viaRank");
    }

    // Color(1) = Green; shift(Green, 5) = 1 + 5 = 6.
    function testViaShift() public {
        require(newTarget().viaShift(1, 5) == 6, "viaShift");
    }

    // Color(2) = Blue; libRank(Blue) = 2 * 10 = 20.
    function testViaLib() public {
        require(newTarget().viaLib(2) == 20, "viaLib");
    }
}
