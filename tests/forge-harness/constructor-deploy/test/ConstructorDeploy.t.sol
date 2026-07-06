// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {
    ConstructorDeployHarnessTarget
} from "../src/ConstructorDeploy.sol";

contract ConstructorDeployForgeTest {
    function testConstructorInitializesState() public {
        ConstructorDeployHarnessTarget target =
            new ConstructorDeployHarnessTarget(4);

        require(target.read() == 5, "value");
    }

    function testConstructorRevertRollsBack() public {
        try new ConstructorDeployHarnessTarget(20) {
            revert("expected revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) == keccak256(bytes("ctor")),
                "reason"
            );
        }
    }
}
