// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {CtorRevertBase} from "../src/CtorRevertBase.sol";

contract CtorRevertBaseTest {
    function test_deploy_reverts_in_base() public {
        try new CtorRevertBase() returns (CtorRevertBase) {
            revert("deploy should have reverted");
        } catch Error(string memory reason) {
            require(keccak256(bytes(reason)) == keccak256(bytes("base zero")),
                    "wrong reason");
        }
    }
}
