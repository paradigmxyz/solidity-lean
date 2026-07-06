// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/CallableIdentity.sol";

contract CallableIdentityForgeTest {
    function testInheritedDominance() public {
        FunctionDominance functionTarget = new FunctionDominance();
        ModifierDominance modifierTarget = new ModifierDominance();

        require(functionTarget.run(10) == 12, "function dominance");
        require(modifierTarget.run(10) == 14, "modifier dominance");
    }

    function testExternalLocationIdentity() public {
        ExternalLocationIdentity target = new ExternalLocationIdentity();
        uint256[] memory values = new uint256[](2);
        values[0] = 17;
        values[1] = 23;

        uint256[] memory result = target.identity(values);
        require(result[0] == 17 && result[1] == 23, "external identity");
    }

    function testResolvedIndependentConflict() public {
        ResolvedIndependentConflict target = new ResolvedIndependentConflict();
        require(target.resolvedValue(10) == 13, "resolved conflict");
    }

    function testOrdinaryOverloads() public {
        CallableIdentity target = new CallableIdentity();
        require(target.runUint(10) == 15, "uint overload");
        require(target.runAddress(address(9)) == 15, "address overload");
    }
}
