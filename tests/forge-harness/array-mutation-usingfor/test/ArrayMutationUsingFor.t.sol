// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ArrayMutationUsingForHarnessTarget} from "../src/ArrayMutationUsingFor.sol";

// Forge ground truth for #135: using-for dispatch of `push`/`pop` on
// memory/calldata array receivers (builtin push/pop are storage-only).
contract ArrayMutationUsingForForgeTest {
    function newTarget() internal returns (ArrayMutationUsingForHarnessTarget) {
        return new ArrayMutationUsingForHarnessTarget();
    }

    function testViaMemoryPop() public {
        require(newTarget().viaMemoryPop() == 3, "viaMemoryPop");
    }

    function testViaMemoryPush() public {
        require(newTarget().viaMemoryPush() == 7, "viaMemoryPush");
    }

    function testViaCalldataPop() public {
        uint256[] memory arg = new uint256[](4);
        require(newTarget().viaCalldataPop(arg) == 4, "viaCalldataPop");
    }
}
