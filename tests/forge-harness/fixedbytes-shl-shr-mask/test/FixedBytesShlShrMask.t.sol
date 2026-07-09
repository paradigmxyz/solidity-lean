// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/FixedBytesShlShrMask.sol";

contract FixedBytesShlShrMaskForgeTest {
    FixedBytesShlShrMask private target;

    function setUp() public {
        target = new FixedBytesShlShrMask();
    }

    function testShlThenShrCleansLane() public view {
        require(target.shlThenShr(0xff) == 0x0f);
    }
}
