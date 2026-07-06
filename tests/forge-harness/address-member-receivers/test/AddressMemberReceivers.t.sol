// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/AddressMemberReceivers.sol";

contract AddressMemberReceiversForgeTest {
    AddressMemberReceivers private target;
    AddressMemberTarget private account;

    function setUp() public {
        target = new AddressMemberReceivers();
        account = new AddressMemberTarget();
    }

    function testAddressEnvironmentMembers() public view {
        address accountAddress = address(account);

        require(target.balanceOf(accountAddress) == accountAddress.balance);
        require(target.codeLength(accountAddress) == accountAddress.code.length);
        require(target.codehashOf(accountAddress) == accountAddress.codehash);
        require(target.identity(accountAddress) == accountAddress);
    }
}
