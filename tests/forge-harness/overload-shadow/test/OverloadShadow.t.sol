// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {OverloadShadowTarget} from "../src/OverloadShadow.sol";

contract OverloadShadowForgeTest {
    OverloadShadowTarget private target = new OverloadShadowTarget();

    // The member `f(uint256)` shadows the same-signature free `f(uint256)`:
    // `g()` must return the member body value (5 + 9 == 14), not the free
    // body value (5 + 1 == 6).
    function testMemberShadowsFree() public view {
        require(target.g() == 14, "member f did not shadow free f");
    }
}
