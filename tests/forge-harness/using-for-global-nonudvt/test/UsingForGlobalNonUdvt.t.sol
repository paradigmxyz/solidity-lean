// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {UsingForGlobalNonUdvt} from "../src/UsingForGlobalNonUdvt.sol";

contract UsingForGlobalNonUdvtForgeTest {
    UsingForGlobalNonUdvt private target = new UsingForGlobalNonUdvt();

    // `a.doubled()` resolves through `using {doubled} for Amount global;`
    // (a struct target) -> 21 * 2 == 42.
    function testGlobalStructMemberDoubled() public view {
        require(target.computeDoubled(21) == 42, "global struct member doubled");
    }

    // `a.plus(8)` -> 21 + 8 == 29 (second brace-list attachment on the struct).
    function testGlobalStructMemberPlus() public view {
        require(target.computePlus(21, 8) == 29, "global struct member plus");
    }
}
