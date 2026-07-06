// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/AddressContractConversions.sol";

contract AddressContractConversionsForgeTest {
    AddressContractConversions private target;

    function setUp() public {
        target = new AddressContractConversions();
    }

    function testAddressToContractConversions() public view {
        address payable payableInput = payable(address(0x1234));
        address ordinaryInput = address(0x5678);

        require(target.toDirectReceive(payableInput) == payableInput);
        require(target.toDirectFallback(payableInput) == payableInput);
        require(target.toInheritedReceive(payableInput) == payableInput);
        require(target.toConstructorOnly(ordinaryInput) == ordinaryInput);
        require(target.toOrdinary(ordinaryInput) == ordinaryInput);
    }

    function testContractValuesToPayableAddress() public view {
        address payable input = payable(address(0x9abc));

        require(
            target.directReceiveValueToPayable(DirectReceiveTarget(input))
                == input
        );
        require(
            target.directFallbackValueToPayable(DirectFallbackTarget(input))
                == input
        );
        require(
            target.inheritedValueToPayable(InheritedReceiveTarget(input))
                == input
        );
    }
}
