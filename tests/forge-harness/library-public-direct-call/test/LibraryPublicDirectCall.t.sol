// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {LibraryPublicDirectCallHarnessTarget} from "../src/LibraryPublicDirectCall.sol";

contract LibraryPublicDirectCallForgeTest {
    LibraryPublicDirectCallHarnessTarget private target =
        new LibraryPublicDirectCallHarnessTarget();

    function testCheckOff() public view {
        require(target.check(0), "check(0) should be true");
    }

    function testCheckOn() public view {
        require(!target.check(1), "check(1) should be false");
    }
}
