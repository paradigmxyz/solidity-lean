// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import {
    ContractCreationHarnessFactory,
    CreatedChild
} from "../src/ContractCreation.sol";

contract ContractCreationForgeTest {
    ContractCreationHarnessFactory private factory =
        new ContractCreationHarnessFactory();

    function testMakeDeploysChild() public {
        CreatedChild child = factory.make(4);
        require(child.read() == 5, "child");
    }
}
