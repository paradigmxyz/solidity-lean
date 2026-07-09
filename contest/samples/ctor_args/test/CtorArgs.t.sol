// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {CtorArgs} from "../src/CtorArgs.sol";

contract CtorArgsTest {
    function test_get() public {
        CtorArgs c = new CtorArgs(21);
        require(c.get() == 42, "v");
    }
}
