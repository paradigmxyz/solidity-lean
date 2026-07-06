// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract DirectReceiveTarget {
    receive() external payable {}
}

contract DirectFallbackTarget {
    fallback() external payable {}
}

contract InheritedReceiveBase {
    receive() external payable {}
}

contract InheritedReceiveTarget is InheritedReceiveBase {}

contract ConstructorOnlyPayableTarget {
    constructor() payable {}
}

contract OrdinaryNonpayableTarget {}

contract AddressContractConversions {
    function toDirectReceive(address payable input)
        external
        pure
        returns (address)
    {
        return address(DirectReceiveTarget(input));
    }

    function toDirectFallback(address payable input)
        external
        pure
        returns (address)
    {
        return address(DirectFallbackTarget(input));
    }

    function toInheritedReceive(address payable input)
        external
        pure
        returns (address)
    {
        return address(InheritedReceiveTarget(input));
    }

    function toConstructorOnly(address input)
        external
        pure
        returns (address)
    {
        return address(ConstructorOnlyPayableTarget(input));
    }

    function toOrdinary(address input)
        external
        pure
        returns (address)
    {
        return address(OrdinaryNonpayableTarget(input));
    }

    function directReceiveValueToPayable(DirectReceiveTarget input)
        external
        pure
        returns (address payable)
    {
        return payable(input);
    }

    function directFallbackValueToPayable(DirectFallbackTarget input)
        external
        pure
        returns (address payable)
    {
        return payable(input);
    }

    function inheritedValueToPayable(InheritedReceiveTarget input)
        external
        pure
        returns (address payable)
    {
        return payable(input);
    }
}
