// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ArrayWidenCopyHarnessTarget} from "../src/ArrayWidenCopy.sol";

contract ArrayWidenCopyForgeTest {
    function testCopyWidenClearsTail() public {
        ArrayWidenCopyHarnessTarget t = new ArrayWidenCopyHarnessTarget();
        (bytes32 a0, bytes32 a1, bytes32 a2) =
            t.copyWidenClearsTail(bytes32(uint256(0x11)), bytes32(uint256(0x22)));
        require(a0 == bytes32(uint256(0x11)), "a0");
        require(a1 == bytes32(uint256(0x22)), "a1");
        require(a2 == bytes32(0), "a2");
    }
}
