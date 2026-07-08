// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

import "../src/AbstractInterfaceId.sol";

contract AbstractInterfaceIdForgeTest {
    AbstractInterfaceIdHarnessTarget private target;

    function setUp() public {
        target = new AbstractInterfaceIdHarnessTarget();
    }

    // Ground-truth: type(AbstractLedger).interfaceId equals the XOR of the
    // external function selectors AND the public state-variable getter selector.
    function testAbstractInterfaceIdValue() public view {
        bytes4 expected = bytes4(keccak256("transfer(address,uint256)"))
            ^ bytes4(keccak256("balanceOf(address)"))
            ^ bytes4(keccak256("totalSupply()"));
        require(target.abstractLedgerId() == expected, "abstract interfaceId");
    }
}
