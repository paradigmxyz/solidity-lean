// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/FixedBytesShlEq.sol";

contract FixedBytesShlEqForgeTest {
    FixedBytesShlEq private target;

    function setUp() public {
        target = new FixedBytesShlEq();
    }

    function testShlEqualsCleansLane() public view {
        require(target.shlEquals(0xff) == true);
    }
}
