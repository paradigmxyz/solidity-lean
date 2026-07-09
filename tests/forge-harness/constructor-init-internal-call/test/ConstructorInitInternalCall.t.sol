// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import { ConstructorInitInternalCall } from "../src/ConstructorInitInternalCall.sol";

contract ConstructorInitInternalCallForgeTest {
    // Initializers call internal functions and run before the body:
    // y = setY() == 7, z = double(y) == 14, then w = y + z == 21.
    function testInitInternalCall() public {
        ConstructorInitInternalCall t = new ConstructorInitInternalCall();
        require(t.y() == 7, "y = setY()");
        require(t.z() == 14, "z = double(y)");
        require(t.w() == 21, "w = y + z");
    }
}
