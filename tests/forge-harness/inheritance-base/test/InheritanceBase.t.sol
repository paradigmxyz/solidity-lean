// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {InheritanceBaseHarnessTarget} from "../src/InheritanceBase.sol";

contract InheritanceBaseForgeTest {
    function testBaseConstructorAndDerivedBody() public {
        InheritanceBaseHarnessTarget target =
            new InheritanceBaseHarnessTarget(4);

        require(target.readBase() == 7, "base");
        require(target.readOwn() == 10, "own");
    }
}
