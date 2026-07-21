// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

import {CtorRevertError} from "../src/CtorRevertError.sol";

contract CtorRevertErrorTest {
    function test_deploy_reverts() public {
        try new CtorRevertError(42) returns (CtorRevertError) {
            revert("deploy should have reverted");
        } catch Error(string memory reason) {
            require(keccak256(bytes(reason)) == keccak256(bytes("ctor bad")),
                    "wrong reason");
        }
    }
}
