// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {StorageArrayPackingTarget} from "../src/StorageArrayPacking.sol";

contract StorageArrayPackingForgeTest {
    StorageArrayPackingTarget private target = new StorageArrayPackingTarget();

    function testRoundTrip() public {
        target.setup();
        for (uint256 i = 0; i < 7; i++) {
            require(target.getA(i) == uint72(0x11 * (i + 1)), "uint72[7] element");
        }
        for (uint256 i = 0; i < 5; i++) {
            require(target.getB(i) == uint96(0x22 * (i + 1)), "uint96[] element");
        }
        for (uint256 i = 0; i < 5; i++) {
            require(target.getC(i) == bytes3(uint24(0x33 * (i + 1))), "bytes3[] element");
        }
        // The trailing scalar must survive: a straddling/undercounting layout
        // would have placed b/c/sentinel at the wrong slots.
        require(target.getSentinel() == 0xdeadbeef, "sentinel clobbered");
    }
}
