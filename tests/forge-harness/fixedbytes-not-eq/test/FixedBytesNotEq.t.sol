// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/FixedBytesNotEq.sol";

contract FixedBytesNotEqForgeTest {
    FixedBytesNotEq private target;

    function setUp() public {
        target = new FixedBytesNotEq();
    }

    function testNotEqualsCleansLane() public view {
        require(target.notEquals(0x0f) == true);
    }
}
