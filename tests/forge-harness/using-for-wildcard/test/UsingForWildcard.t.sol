// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {UsingForWildcardHarnessTarget} from "../src/UsingForWildcard.sol";

// Forge ground truth for G20: dispatch through `using WildcardLib for *`.
contract UsingForWildcardForgeTest {
    function newTarget() internal returns (UsingForWildcardHarnessTarget) {
        return new UsingForWildcardHarnessTarget();
    }

    function testViaUint() public {
        require(newTarget().viaUint(21) == 42, "viaUint");
    }

    function testViaInt() public {
        require(newTarget().viaInt(-4) == -12, "viaInt");
    }

    function testViaBytes() public {
        require(newTarget().viaBytes(hex"aabbcc", 10) == 13, "viaBytes");
    }

    function testViaBool() public {
        require(newTarget().viaBool(false) == true, "viaBool");
    }
}
