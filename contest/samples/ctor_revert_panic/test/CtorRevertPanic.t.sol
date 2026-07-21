// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {CtorRevertPanic} from "../src/CtorRevertPanic.sol";

contract CtorRevertPanicTest {
    function test_deploy_panics() public {
        try new CtorRevertPanic() returns (CtorRevertPanic) {
            revert("deploy should have reverted");
        } catch Panic(uint256 code) {
            require(code == 0x11, "wrong panic code");
        }
    }
}
