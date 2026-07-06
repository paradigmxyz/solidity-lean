// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {ModifierOrderHarnessTarget} from "../src/ModifierOrder.sol";

contract ModifierOrderForgeTest {
    ModifierOrderHarnessTarget private target =
        new ModifierOrderHarnessTarget();

    function testModifierOrder() public {
        target.run(5);
        require(target.read() == 106, "order");
    }

    function testModifierRollback() public {
        try target.blocked() {
            revert("expected revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) == keccak256(bytes("gate")),
                "reason"
            );
            require(target.read() == 0, "rollback");
        }
    }
}
